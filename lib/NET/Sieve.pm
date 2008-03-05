package NET::Sieve;
use strict;
use warnings;

use Authen::SASL qw(Perl); # Need a way to ask which mechanism to send
use Authen::SASL::Perl::EXTERNAL; # We munge inside its private stuff.
use Errno;
use IO::Socket::INET6;
use IO::Socket::SSL 0.97; # SSL_ca_path bogus before 0.97
use MIME::Base64;
use POSIX qw/ strftime /;
use NET::Sieve::Script;

BEGIN {
    use Exporter ();
    use vars qw($VERSION @ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);
    $VERSION     = '0.01';
    @ISA         = qw(Exporter);
    #Give a hoot don't pollute, do not export more than needed by default
    @EXPORT      = qw();
    @EXPORT_OK   = qw();
    %EXPORT_TAGS = ();
}


#################### subroutine header begin ####################

=head2 sample_function

 Usage     : How to use this function/method
 Purpose   : What it does
 Returns   : What it returns
 Argument  : What it wants to know
 Throws    : Exceptions and other anomolies
 Comment   : This is a sample subroutine header.
           : It is polite to include more pod and fewer comments.

See Also   : 

=cut

#################### subroutine header end ####################

my %capa;
my %raw_capabilities;
my %capa_dosplit = map {$_ => 1} qw( SASL SIEVE );
my $DEBUGGING = 1;

sub new
{
    my ($class, %param) = @_;

    my $self = bless ({}, ref ($class) || $class);

my $server = $param{server};
my $port = $param{port}||'sieve(2000)';
my $net_domain = $param{net_domain}||AF_UNSPEC;
my $user = $param{user};
my $sslkeyfile =  $param{sslkeyfile};
my $sslcertfile =  $param{sslcertfile};
my $realm = $param{realm};
my $authmech = $param{realm};
my $authzid = $param{authzid};
my $passwordfd = $param{passwordfd};
my $prompt_for_password = $param{password};
my $ssl_verify = $param{ssl_verif} || '0x01';
$DEBUGGING = $param{debug};

my %ssl_options = (
        SSL_version     => 'TLSv1',
        SSL_cipher_list => 'ALL:!NULL:!LOW:!EXP:!ADH:@STRENGTH',
        SSL_verify_mode => $ssl_verify,
        SSL_ca_path     => '/etc/ssl/certs',
);

my $prioritise_auth_external = 0;
my ($forbid_clearauth, $forbid_clearchan) = (0, 0);

unless (defined $server) {
        $server = 'localhost';
        if (exists $ENV{'IMAP_SERVER'}
                        and $ENV{'IMAP_SERVER'} !~ m!^/!) {
                $server = $ENV{'IMAP_SERVER'};
                # deal with a port number.
                unless ($server =~ /:.*:/) { # IPv6 address literal
                        $server =~ s/:\d+\z//;
                }
        }
}

die "Bad server name\n"
        unless $server =~ /^[A-Za-z0-9_.-]+\z/;
die "Bad port specification\n"
        unless $port =~ /^[A-Za-z0-9_()-]+\z/;

unless (defined $user) {
        if ($^O eq "MSWin32") {
                # perlvar documents always "MSWin32" on Windows ...
                # what about 64bit windows?
                if (exists $ENV{USERNAME} and length $ENV{USERNAME}) {
                        $user = $ENV{USERNAME};
                } elsif (exists $ENV{LOGNAME} and length $ENV{LOGNAME}) {
                        $user = $ENV{LOGNAME};
                } else {
                        die "Unable to figure out a default user, sorry.\n";
                }
        } else {
                $user = getpwuid $>;
        }
        # this should handle the non-mswin32 case if 64bit _is_ different.
        die "Unable to figure out a default user, sorry!\n"
                unless defined $user;
}

if ((defined $sslkeyfile and not defined $sslcertfile) or
    (defined $sslcertfile and not defined $sslkeyfile)) {
        die "Need both a client key and cert for SSL certificate auth.\n";
}
if (defined $sslkeyfile) {
        $ssl_options{SSL_use_cert} = 1;
        $ssl_options{SSL_key_file} = $sslkeyfile;
        $ssl_options{SSL_cert_file} = $sslcertfile;
        $prioritise_auth_external = 1;
}


my $sock = IO::Socket::INET6->new(
        PeerHost        => $server,
        PeerPort        => $port,
        Proto           => 'tcp',
        Domain          => $net_domain,
        MultiHomed      => 1, # try multiple IPs (IPv4 works, v6 doesn't?)
);
unless (defined $sock) {
        my $extra = '';
        if ($!{EINVAL} and $net_domain != AF_UNSPEC) {
          $extra = " (Probably no host record for overriden IP version)\n";
        }
        die qq{Connection to "$server" [port $port] failed: $!\n$extra};
}

$sock->autoflush(1);
_debug("connection: remote host address is @{[$sock->peerhost()]}");

$self->{_sock} = $sock;

_parse_capabilities($sock);

if (exists $capa{STARTTLS}) {
        $self->ssend("STARTTLS");
        $self->sget();
        die "STARTTLS request rejected: $_\n" unless /^OK\s+\"/;
        IO::Socket::SSL->start_SSL($sock, %ssl_options) or do {
                my $e = IO::Socket::SSL::errstr();
                die "STARTTLS promotion failed: $e\n";
        };
        _debug("--- TLS activated here");
        $forbid_clearauth = 0;
        # Cyrus sieve might send CAPABILITY after STARTTLS without being
        # prompted for it.  This breaks the command-response model.
        # We can't just check to see if there's data to read or not, since
        # that will break if the next data is delayed (race condition).
        # There is no protocol-compliant method to determine this, short
        # of "wait a while, see if anything comes along; if not, send
        # CAPABILITY ourselves".  So, I break protocol by sending the
        # non-existent command NOOP, then scan for the resulting NO.
        $self->ssend("NOOP");
        _parse_capabilities($sock,
                until_see_no    => 1,
                external_first => $prioritise_auth_external);
        unless (scalar keys %capa) {
                $self->ssend("CAPABILITY");
                _parse_capabilities($sock,
                        external_first => $prioritise_auth_external);
        }
} elsif ($forbid_clearchan) {
        die "TLS not offered, SASL confidentiality not supported in client.\n";
}

my %authen_sasl_params;
$authen_sasl_params{callback}{user} = $user;
if (defined $authzid) {
        $authen_sasl_params{callback}{authname} = $authzid;
}
if (defined $realm) {
        # for compatibility, we set it as a callback AND as a property (below)
        $authen_sasl_params{callback}{realm} = $realm;
}

if (defined $passwordfd) {
        open(PASSHANDLE, "<&=", $passwordfd)
                or die "Unable to open fd $passwordfd for reading: $!\n";
        my @data = <PASSHANDLE>;
        close(PASSHANDLE);
        chomp $data[-1];
        $authen_sasl_params{callback}{pass} = join '', @data;
} else {
        $authen_sasl_params{callback}{pass} = $prompt_for_password;
}

$self->closedie("Do not have an authentication mechanism list\n")
        unless ref($capa{SASL}) eq 'ARRAY';
if (defined $authmech) {
        $authmech = uc $authmech;
        if (grep {$_ eq $authmech} map {uc $_} @{$capa{SASL}}) {
                _debug("auth: will try requested SASL mechanism $authmech");
        } else {
                $self->closedie("Server does not offer SASL mechanism $authmech\n");
        }
        $authen_sasl_params{mechanism} = $authmech;
} else {
        $authen_sasl_params{mechanism} = $raw_capabilities{SASL};
}

my $sasl = Authen::SASL->new(%authen_sasl_params);
die "SASL object init failed (local problem): $!\n"
        unless defined $sasl;

my $secflags = 'noanonymous';
$secflags .= ' noplaintext' if $forbid_clearauth;
my $authconversation = $sasl->client_new('sieve', $server, $secflags)
        or die "SASL conversation init failed (local problem): $!\n";
if (defined $realm) {
        $authconversation->property(realm => $realm);
}
{
        my $sasl_m = $authconversation->mechanism()
                or die "Oh why can't I decide which auth mech to send?\n";
        if ($sasl_m eq 'GSSAPI') {
                _debug("-A- GSSAPI sasl_m <temp>");
                # gross hack, but it was bad of us to assume anything.
                # It also means that we ignore anything specified by the
                # user, which is good since it's Kerberos anyway.
                # (Major Assumption Alert!)
                $authconversation->callback(
                        user => undef,
                        pass => undef,
                );
        }

        my $sasl_tosend = $authconversation->client_start();
        if ($authconversation->code()) {
                my $emsg = $authconversation->error();
                $self->closedie("SASL Error: $emsg\n");
        }

        if (defined $sasl_tosend and length $sasl_tosend) {
                my $mimedata = encode_base64($sasl_tosend, '');
                my $mlen = length($mimedata);
                $self->ssend ( qq!AUTHENTICATE "$sasl_m" {${mlen}+}! );
                $self->ssend ( $mimedata );
        } else {
                $self->ssend ( qq{AUTHENTICATE "$sasl_m"} );
        }
        $self->sget();

        while ($_ !~ /^(OK|NO)(?:\s.*)?$/m) {
                my $challenge;
                if (/^"(.*)"\r?\n?$/) {
                        $challenge = $1;
                } else {
                        unless (/^{(\d+)\+?}\r?$/m) {
                                $self->sfinish ( "*" );
                                $self->closedie ("Failure to parse server SASL response.\n");
                        }
                        ($challenge = $_) =~ s/^{\d+\+?}\r?\n?//;
                }
                $challenge = decode_base64($challenge);

                my $response = $authconversation->client_step($challenge);
                if ($authconversation->code()) {
                        my $emsg = $authconversation->error();
                        $self->closedie("SASL Error: $emsg\n");
                }
                $response = '' unless defined $response; # sigh
                my $senddata = encode_base64($response, '');
                my $sendlen = length $senddata;
                $self->ssend ( "{$sendlen+}" );
                # okay, we send a blank line here even for 0 length data
                $self->ssend ( $senddata );
                $self->sget();
        }

        if (/^NO((?:\s.*)?)$/) {
                $self->closedie_NOmsg($1, "Authentication refused by server");
        }
        if (/^OK\s+\(SASL\s+\"([^"]+)\"\)$/) {
                # This _should_ be pre_sent with server-verification steps which
                # in other profiles expect an empty response.  But Authen::SASL
                # doesn't let us confirm that we've finished authentication!
                # The assumption seems to be that the server only verifies us
                # so if it says "okay", we don't keep trying.
                my $final_auth = decode_base64($1);
                my $valid = $authconversation->client_step($final_auth);
                # Skip checking $authconversation->code() here because
                # Authen::SASL::Perl::DIGEST-MD5 module will complain at this
                # final step:
                #   Server did not provide required field(s): algorithm nonce
                # which is bogus -- it's not required or expected.
                if (defined $valid and length $valid) {
                        $self->closedie("Server failed final verification");
                }
        }

}

    return $self;
};
#############
# public methods

sub list
{
    my $self = shift;
    my @list_script_names;
    my $sock = $self->{_sock};
    $self->ssend("LISTSCRIPTS");
    $self->sget();
    while (/^\"/) {
        my $line =  $_;
         my $name = $1 if ($line =~ m/\"(.*?)\"/);
         my $status = ($line =~ m/ACTIVE/) ? 1 : 0;
         my $script = NET::Sieve::Script->new(name => $name, status => $status);
         push @list_script_names,$script;
         $self->sget();
         }

    return \@list_script_names;
}

sub put
{
    my $self = shift;
    my $script = shift;

    my $sock = $self->{_sock};

    my $size = length($script->raw);
    return 0 if (!$size);

    $self->ssend('PUTSCRIPT "'.$script->name.'" {'.$size.'+}');
    $self->ssend('-noeol', $script->raw);
    $self->ssend('');
    $self->sget();

    unless (/^OK((?:\s.*)?)$/) {
       warn "PUTSCRIPT(".$script->name.") failed: $_\n";
    }

    return 1;
}
#  my $sieve = ...
#  my $script = NET::Sieve::Script->new(name => 'test');
#     $script->raw ( $sieve->get('test') );
sub get
{
    my $self = shift;
    my $name = shift;

    $self->ssend("GETSCRIPT \"$name\"");
    $self->sget();
        if (/^NO((?:\s.*)?)$/) {
                die_NOmsg($1, qq{Script "$name" not returned by server});
        }
        if (/^OK((?:\s.*)?)$/) {
                warn qq{Empty script "$name"?  Not saved.\n};
                return;
        }
        unless (/^{(\d+)}\r?$/m) {
                die "QUIT:Failed to parse server response to GETSCRIPT";
        }
        my $contentdata = $_;
        $self->sget();
        while (/^$/) { $self->sget(); } # extra newline but only for GETSCRIPT?
        unless (/^OK((?:\s.*)?)$/) { 
                die_NOmsg $_, "Script retrieval not successful, not saving";
        }
        $contentdata =~ s/^{\d+\+?}\r?\n?//m;
        
    return $contentdata;
}
###################
# private methods
#functions

sub _parse_capabilities
{
        my $sock = shift;
        local %_ = @_;
        my $external_first = 0;
        $external_first = $_{external_first} if exists $_{external_first};

        %raw_capabilities = ();
        %capa = ();
        while (<$sock>) {
                chomp; s/\s*$//;
                _received();
                if (/^OK$/) {
                        last unless exists $_{until_see_no};
                } elsif (/^\"([^"]+)\"\s+\"(.+)\"$/) {
                        my ($k, $v) = ($1, $2);
                        $raw_capabilities{$k} = $v;
                        $capa{$k} = $v;
                        if (exists $capa_dosplit{$k}) {
                                $capa{$k} = [ split /\s+/, $v ];
                        }
                } elsif (/^\"([^"]+)\"$/) {
                        $raw_capabilities{$1} = '';
                        $capa{$1} = 1;
                } elsif (/^NO/) { 
                        last if exists $_{until_see_no};
                        warn "Unhandled server line: $_\n"
                } else {
                        warn "Unhandled server line: $_\n"
                }
        };

        if (exists $capa{SASL} and $external_first
                        and grep {uc($_) eq 'EXTERNAL'} @{$capa{SASL}}) {
                # We do two things.  We shift the EXTERNAL to the head of the
                # list, suggesting that it's the server's preferred choice.
                # We then mess around inside the Authen::SASL::Perl::EXTERNAL
                # private stuff (name starts with an underscore) to bump up
                # its priority -- for some reason, the method which is not
                # interactive and says "use information already available"
                # is less favoured than some others.
                _debug("auth: shifting EXTERNAL to start of mechanism list");
                my @sasl = ('EXTERNAL');
                foreach (@{$capa{SASL}}) {
                        push @sasl, $_ unless uc($_) eq 'EXTERNAL';
                }
                $capa{SASL} = \@sasl;
                $raw_capabilities{SASL} = join(' ', @sasl);
                no warnings 'redefine';
                $Authen::SASL::Perl::EXTERNAL::{_order} = sub { 10 };
        }
}

sub _debug
{
        return unless $DEBUGGING;
        print STDERR "$_[0]\n";
}

sub _sent { $_[0] = $_ unless defined $_[0]; _debug ">>> $_[0]"; }
sub _received { $_[0] = $_ unless defined $_[0]; _debug "<<< $_[0]"; }

# ######################################################################
# minor private routines


sub ssend
{
        my $self = shift;
        my $sock = $self->{_sock};
        #my $sock = shift;
        my $eol = "\r\n";
        if (defined $_[0] and $_[0] eq '-noeol') {
                shift;
                $eol = '';
        }
        foreach my $l (@_) {
                $sock->print("$l$eol");
# yes, the _debug output can have extra blank lines if supplied -noeol because
# they're already pre_sent.  Rather than mess around to tidy it up, I'm leaving
# it because it's _debug output, not UI or protocol text.
                _sent ( $l );
        }
}

sub sget
{
        my $self = shift;
        my $sock = $self->{_sock};
        my $dochomp = 1;
        $dochomp = 0 if defined $_[0] and $_[0] eq '-nochomp';
        my $l;
        $l = $sock->getline();
        if ($l =~ /{(\d+)\+?}\s*\n?\z/) {
                _debug("... literal string response, length $1");
                my $len = $1;
                if ($len == 0) {
                        my $discard = $sock->getline();
                } else {
                        while ($len > 0) {
                                my $extra = $sock->getline();
                                $len -= length($extra);
                                $l .= $extra;
                        }
                }
                $dochomp = 0;
        }
        if ($dochomp) {
                chomp $l; $l =~ s/\s*$//;
        }
        _received $l;
        if (defined wantarray) {
                return $l;
        } else {
                $_ = $l;
        }
}

sub sfinish
{
        my $self = shift;
        my $sock = $self->{_sock};
        if (defined $_[0]) {
                $self->ssend($sock, $_[0]);
                $self->sget();
        }
        $self->ssend($sock, "LOGOUT");
        $self->sget();
}

sub closedie
{
        my $self = shift;
        my $sock = $self->{_sock};
        my $e = $!;
        $self->sfinish();
        $! = $e;
        die @_;
}

sub closedie_NOmsg
{
        my $self = shift;
        my $sock = $self->{_sock};
        my $suffix = shift;
        if (length $suffix) {
                $suffix = ':' . $suffix;
        } else {
                $suffix = '.';
        }
        $self->closedie($_[0] . $suffix . "\n");
}

sub die_NOmsg
{
        my $suffix = shift;
        my $msg = shift;
        if (length $suffix) {
                $msg .= ':' . $suffix . "\n";
        } else {
                $msg .= ".\n";
        }
        die $msg;
}


#################### main pod documentation begin ###################
## Below is the stub of documentation for your module. 
## You better edit it!


=head1 NAME

NET::Sieve - Module abstract (<= 44 characters) goes here

=head1 SYNOPSIS

  use NET::Sieve;
  blah blah blah


=head1 DESCRIPTION

Stub documentation for this module was created by ExtUtils::ModuleMaker.
It looks like the author of the extension was negligent enough
to leave the stub unedited.

Blah blah blah.


=head1 USAGE



=head1 BUGS



=head1 SUPPORT



=head1 AUTHOR

    Yves
    CPAN ID: YVESAGO
    Univ Metz
    agostini@univ-metz.fr
    http://www.crium.univ-metz.fr

=head1 COPYRIGHT

This program is free software; you can redistribute
it and/or modify it under the same terms as Perl itself.

The full text of the license can be found in the
LICENSE file included with this module.


=head1 SEE ALSO

perl(1).

=cut

#################### main pod documentation end ###################


1;
# The preceding line will help the module return a true value
