use inc::Module::Install;

name		'NET-Sieve';
all_from	'lib/NET/Sieve.pm';

requires 'Authen::SASL';
requires 'IO::Socket::INET6';
requires 'IO::Socket::SSL';
requires 'MIME::Base64';

auto_install;

tests('t/*.t');

WriteAll;

