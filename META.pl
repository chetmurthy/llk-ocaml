#!/usr/bin/env perl

use strict ;
BEGIN { push (@INC, "..") }
use Version ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_llk" preprocessor:
requires = "camlp5,bos,fmt,pa_ppx.base"
version = "$Version::version"
description = "pa_ppx pa_llk support"

# For linking
package "link" (
requires = "camlp5,bos,fmt,pa_ppx.base.link"
archive(byte) = "pa_llk.cma"
archive(native) = "pa_llk.cmxa"
)

# For the toploop:
archive(byte,toploop) = "pa_llk.cma"

  # For the preprocessor itself:
  requires(syntax,preprocessor) = "camlp5,bos,fmt,pa_ppx.base"
  archive(syntax,preprocessor,-native) = "pa_llk.cma"
  archive(syntax,preprocessor,native) = "pa_llk.cmxa"

EOF
