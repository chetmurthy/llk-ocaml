#!/usr/bin/env perl

use strict ;
BEGIN { push (@INC, "..") }
use Version ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_llk_compiler" preprocessor:
requires = "camlp5,bos,fmt,pa_ppx.base"
version = "$Version::version"
description = "pa_llk compiler"

# For linking
package "link" (
requires = "camlp5,bos,fmt,pa_ppx.base.link"
archive(byte) = "pa_llk_compiler.cma"
archive(native) = "pa_llk_compiler.cmxa"
)

# For the toploop:
archive(byte,toploop) = "pa_llk_compiler.cma"

  # For the preprocessor itself:
  requires(syntax,preprocessor) = "camlp5,bos,fmt,pa_ppx.base"
  archive(syntax,preprocessor,-native) = "pa_llk_compiler.cma"
  archive(syntax,preprocessor,native) = "pa_llk_compiler.cmxa"

EOF
