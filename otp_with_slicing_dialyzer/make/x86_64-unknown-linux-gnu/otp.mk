#-*-makefile-*-   ; force emacs to enter makefile-mode
# ----------------------------------------------------
# Make include file for otp
#
# %CopyrightBegin%
#
# Copyright Ericsson AB 1997-2011. All Rights Reserved.
#
# The contents of this file are subject to the Erlang Public License,
# Version 1.1, (the "License"); you may not use this file except in
# compliance with the License. You should have received a copy of the
# Erlang Public License along with this software. If not, it can be
# retrieved online at http://www.erlang.org/.
#
# Software distributed under the License is distributed on an "AS IS"
# basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
# the License for the specific language governing rights and limitations
# under the License.
#
# %CopyrightEnd%
#
# Author: Lars Thorsen
# ----------------------------------------------------
.SUFFIXES: .erl .beam .yrl .xrl .bin .mib .hrl .sgml .xml .xmlsrc .html .ps \
	.3 .1 .fig .dvi .tex .class .java .pdf .fo .psframe .pscrop .el .elc

# ----------------------------------------------------
#	Cross Compiling
# ----------------------------------------------------
CROSS_COMPILING = no

# ----------------------------------------------------
#	Common macros
# ----------------------------------------------------
DEFAULT_TARGETS =  opt debug release release_docs clean docs

# Slash separated list of return values from $(origin VAR)
# that are untrusted - set default in this file instead.
# The list is not space separated since some return values
# contain space, and we want to use $(findstring ...) to
# search the list.
DUBIOUS_ORIGINS = /undefined/environment/

# ----------------------------------------------------
#	HiPE
# ----------------------------------------------------

HIPE_ENABLED=yes
NATIVE_LIBS_ENABLED=

# ----------------------------------------------------
#	Command macros
# ----------------------------------------------------
INSTALL         = /usr/bin/install -c
INSTALL_DIR     = /usr/bin/install -c -d
INSTALL_PROGRAM = ${INSTALL}
INSTALL_SCRIPT  = ${INSTALL}
INSTALL_DATA    = ${INSTALL} -m 644

CC = gcc
GCC = yes
HCC = $(CC)
CC32 = gcc
CFLAGS32 = -g -O2 -I/home/kostis/slice/otp_src_R14B04+slice/erts/x86_64-unknown-linux-gnu   -fno-tree-copyrename  -D_GNU_SOURCE -m32
BASIC_CFLAGS = -g -O2 -I/home/kostis/slice/otp_src_R14B04+slice/erts/x86_64-unknown-linux-gnu   -fno-tree-copyrename  -D_GNU_SOURCE
DEBUG_FLAGS =  -g
LD = $(CC)
RANLIB = ranlib
AR = ar
PERL = /usr/bin/perl

BITS64 = yes

OTP_RELEASE = 

# ----------------------------------------------------
#	Erlang language section
# ----------------------------------------------------
EMULATOR = beam
ifeq ($(findstring vxworks,$(TARGET)),vxworks)
# VxWorks object files should be compressed.
# Other object files should have debug_info.
  ERL_COMPILE_FLAGS += +compressed
else
  ifeq ($(findstring ose_ppc750,$(TARGET)),ose_ppc750)
    ERL_COMPILE_FLAGS += +compressed
  else
    ifdef BOOTSTRAP
      ERL_COMPILE_FLAGS += +slim
    else
      ERL_COMPILE_FLAGS += +debug_info
    endif
  endif
endif
ERLC_WFLAGS = -W
ERLC = erlc $(ERLC_WFLAGS) $(ERLC_FLAGS)
ERL = erl -boot start_clean

ifneq (,$(findstring $(origin EBIN),$(DUBIOUS_ORIGINS)))
EBIN = ../ebin
endif

# Generated (non ebin) files...
ifneq (,$(findstring $(origin EGEN),$(DUBIOUS_ORIGINS)))
EGEN = .
endif

ifneq (,$(findstring $(origin ESRC),$(DUBIOUS_ORIGINS)))
ESRC = .
endif

$(EBIN)/%.beam: $(EGEN)/%.erl
	$(ERLC) $(ERL_COMPILE_FLAGS) -o$(EBIN) $<

$(EBIN)/%.beam: $(ESRC)/%.erl
	$(ERLC) $(ERL_COMPILE_FLAGS) -o$(EBIN) $<

.erl.beam:
	$(ERLC) $(ERL_COMPILE_FLAGS) -o$(dir $@) $<

#
# When .erl files are automatically created GNU make removes them if
# they were the result of a chain of implicit rules. To prevent this
# we say that all .erl files are "precious".
#
.PRECIOUS: %.erl %.fo

## Uncomment these lines and add .idl to suffixes above to have erlc 
## eat IDL files
##$(EGEN)/%.erl: $(ESRC)/%.idl
##	$(ERLC) $(IDL_FLAGS) $<

$(EGEN)/%.erl: $(ESRC)/%.yrl
	$(ERLC) $(YRL_FLAGS) -o$(EGEN) $<

$(EGEN)/%.erl: $(ESRC)/%.xrl
	$(ERLC) $(XRL_FLAGS) -o$(EGEN) $<

# ----------------------------------------------------
#	SNMP language section
# ----------------------------------------------------
SNMP_TOOLKIT = $(ERL_TOP)/lib/snmp
ifeq ($(SNMP_BIN_TARGET_DIR),)
  SNMP_BIN_TARGET_DIR = ../priv/mibs
endif
ifeq ($(SNMP_HRL_TARGET_DIR),)
  SNMP_HRL_TARGET_DIR = ../include
endif


$(SNMP_BIN_TARGET_DIR)/%.bin: %.mib
	$(ERLC) -pa $(SNMP_TOOLKIT)/ebin -I $(SNMP_TOOLKIT)/priv/mibs $(SNMP_FLAGS) -o $(SNMP_BIN_TARGET_DIR) $<

$(SNMP_HRL_TARGET_DIR)/%.hrl: $(SNMP_BIN_TARGET_DIR)/%.bin
	$(ERLC) -pa $(SNMP_TOOLKIT)/ebin -o $(SNMP_HRL_TARGET_DIR) $<

.mib.bin:
	$(ERLC) -pa $(SNMP_TOOLKIT)/ebin -I $(SNMP_TOOLKIT)/priv/mibs $(SNMP_FLAGS) $<

.bin.hrl:
	$(ERLC) -pa $(SNMP_TOOLKIT)/ebin $<

# ----------------------------------------------------
#	Java language section
# ----------------------------------------------------
JAVA= javac

ifneq (,$(findstring $(origin JAVA_DEST_ROOT),$(DUBIOUS_ORIGINS)))
JAVA_DEST_ROOT = ../priv/
endif

.java.class:
	CLASSPATH=$(CLASSPATH) $(JAVA) $(JAVA_OPTIONS) $<


$(JAVA_DEST_ROOT)$(JAVA_CLASS_SUBDIR)%.class: %.java
	CLASSPATH=$(CLASSPATH) $(JAVA) $(JAVA_OPTIONS) -d $(JAVA_DEST_ROOT) $<

# ----------------------------------------------------
#	Emacs byte code compiling
# ----------------------------------------------------
EMACS_COMPILER=emacs-20
EMACS_COMPILE_OPTIONS=-q --no-site-file -batch -f batch-byte-compile

.el.elc:
	$(EMACS_COMPILER) $(EMACS_COMPILE_OPTIONS) $<

# ----------------------------------------------------
#	Documentation section
# ----------------------------------------------------
export VSN

DOCSUPPORT = 1

TOPDOCDIR=../../../../doc

DOCDIR = ..

PDFDIR=$(DOCDIR)/pdf

HTMLDIR = $(DOCDIR)/html

MAN1DIR = $(DOCDIR)/man1
MAN2DIR = $(DOCDIR)/man2
MAN3DIR = $(DOCDIR)/man3
MAN4DIR = $(DOCDIR)/man4
MAN6DIR = $(DOCDIR)/man6
MAN9DIR = $(DOCDIR)/man9

TEXDIR = .

SPECDIR = $(DOCDIR)/specs

# HTML & GIF files that always are generated and must be delivered 
SGML_COLL_FILES = $(SGML_APPLICATION_FILES) $(SGML_PART_FILES)
XML_COLL_FILES = $(XML_APPLICATION_FILES) $(XML_PART_FILES)
DEFAULT_HTML_FILES = \
	$(SGML_COLL_FILES:%.sgml=$(HTMLDIR)/%_frame.html) \
	$(SGML_COLL_FILES:%.sgml=$(HTMLDIR)/%_first.html) \
	$(SGML_COLL_FILES:%.sgml=$(HTMLDIR)/%_term.html) \
	$(SGML_COLL_FILES:%.sgml=$(HTMLDIR)/%_cite.html) \
	$(SGML_APPLICATION_FILES:%.sgml=$(HTMLDIR)/%_index.html) \
	$(SGML_APPLICATION_FILES:%.sgml=$(HTMLDIR)/%.kwc) \
	$(XML_COLL_FILES:%.xml=$(HTMLDIR)/%_frame.html) \
	$(XML_COLL_FILES:%.xml=$(HTMLDIR)/%_first.html) \
	$(XML_COLL_FILES:%.xml=$(HTMLDIR)/%_term.html) \
	$(XML_COLL_FILES:%.xml=$(HTMLDIR)/%_cite.html) \
	$(XML_APPLICATION_FILES:%.xml=$(HTMLDIR)/%_index.html) \
	$(XML_APPLICATION_FILES:%.xml=$(HTMLDIR)/%.kwc) \
	$(HTMLDIR)/index.html

DEFAULT_GIF_FILES = $(HTMLDIR)/min_head.gif

#
# Flags & Commands
#
XSLTPROC = xsltproc
FOP = fop

DOCGEN=$(ERL_TOP)/lib/erl_docgen

ifneq (,$(findstring $(origin SPECS_ESRC),$(DUBIOUS_ORIGINS)))
SPECS_ESRC = ../../src
endif
SPECS_EXTRACTOR=$(DOCGEN)/priv/bin/specs_gen.escript
# Extract specifications and types from Erlang source files (-spec, -type)
$(SPECDIR)/specs_%.xml: $(SPECS_ESRC)/%.erl
	escript $(SPECS_EXTRACTOR) $(SPECS_FLAGS) -o$(dir $@) $<


$(MAN1DIR)/%.1: %.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<


$(MAN2DIR)/%.2: %.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<


ifneq ($(wildcard $(SPECDIR)),)
$(MAN3DIR)/%.3: %.xml $(SPECDIR)/specs_%.xml
	date=`date +"%B %e %Y"`; \
	specs_file=`pwd`/$(SPECDIR)/specs_$*.xml; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --stringparam specs_file "$$specs_file" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<
else
$(MAN3DIR)/%.3: %.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<
endif

# left for compatibility
$(MAN4DIR)/%.4: %.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<

$(MAN4DIR)/%.5: %.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<

# left for compatibility
$(MAN6DIR)/%.6: %_app.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<

$(MAN6DIR)/%.7: %_app.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<

$(MAN9DIR)/%.9: %.xml
	date=`date +"%B %e %Y"`; \
	xsltproc --output "$@" --stringparam company "Ericsson AB" --stringparam docgen "$(DOCGEN)" --stringparam gendate "$$date" --stringparam appname "$(APPLICATION)" --stringparam appver "$(VSN)" --xinclude -path $(DOCGEN)/priv/docbuilder_dtd  -path $(DOCGEN)/priv/dtd_man_entities $(DOCGEN)/priv/xsl/db_man.xsl $<


.xmlsrc.xml:
	 escript $(DOCGEN)/priv/bin/codeline_preprocessing.escript $< $@

.fo.pdf:
	$(FOP) -fo $< -pdf $@

