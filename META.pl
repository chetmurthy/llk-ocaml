#!/usr/bin/env perl

use strict ;
use IPC::System::Simple qw(systemx runx capturex $EXITVAL);
use String::ShellQuote ;
use File::Basename;

use Version ;

our %pkgmap = (
  'pa_llk_compiler' => 'pa_llk.compiler',
  'pa_llk_runtime' => 'pa_llk.runtime',
  
    );

{
  my $compmeta = indent(2, fixdeps(capturex("./pa_llk/META.pl"))) ;
  my $rtmeta = indent(2, fixdeps(capturex("./runtime/META.pl"))) ;

  print <<"EOF";
version = "$Version::version"
description = "pa_llk: camlp5-based LLK parser generator"

package "compiler" (
$compmeta
)

package "runtime" (
$rtmeta
)

EOF
}

sub fixdeps {
  my $txt = join('', @_) ;
  $txt =~ s,^(.*require.*)$, fix0($1) ,mge;
  return $txt ; 
}

sub fix0 {
  my $txt = shift ;
  $txt =~ s,"([^"]+)", '"'. fix($1) .'"' ,e;
  return $txt ;
}

sub fix {
  my $txt = shift ;
  my @l = split(/,/,$txt);
  my @ol = () ;
  foreach my $p (@l) {
    $p =~ s,^([^.]+), $pkgmap{$1} || $1 ,e ;
    push(@ol, $p);
  }
  $txt = join(',', @ol) ;
  return $txt ;
}

sub indent {
  my $n = shift ;
  my $txt = shift ;
  my $pfx = ' ' x $n ;
  $txt =~ s,^,$pfx,gm;
  return $txt ;
}
