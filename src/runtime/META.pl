#!/usr/bin/env perl

use strict ;
BEGIN { push (@INC, "..") }
use Version ;

our $destdir = shift @ARGV ;

print <<"EOF";
# Specifications for the "pa_llk_runtime":
requires = "result,rresult,fmt"
version = "$Version::version"
description = "pa_llk runtime support"

# For linking
archive(byte) = "pa_llk_runtime.cma"
archive(native) = "pa_llk_runtime.cmxa"

# For the toploop:
archive(byte,toploop) = "pa_llk_runtime.cma"

EOF
