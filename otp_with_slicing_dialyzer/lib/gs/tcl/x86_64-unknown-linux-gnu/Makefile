#
# %CopyrightBegin%
# 
# Copyright Ericsson AB 2002-2009. All Rights Reserved.
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

#
include $(ERL_TOP)/make/target.mk
include $(ERL_TOP)/make/$(TARGET)/otp.mk

# ----------------------------------------------------
# Application version
# ----------------------------------------------------
include ../vsn.mk
VSN=$(GS_VSN)

# ----------------------------------------------------
# The following variables differ on different systems, we set
# reasonable defaults, if something different is needed it should
# be set for that system only.
# ----------------------------------------------------

ifeq ($(TARGET),win32)
TCL_TAR = binaries/win32.tar.gz
else
TCL_TAR = 
endif

CONFIGURE_FILES = ../configure ../configure.in

ROOTDIR = ..
BINDIR = $(ROOTDIR)/priv/bin
LIBDIR = ./lib

RELSYSDIR = $(RELEASE_PATH)/lib/gs-$(VSN)

# ----------------------------------------------------
# Common Macros
# ----------------------------------------------------
TCL_FILES   = ../priv/gstk.tcl
EXTRA_FILES = ../priv/gs-xdefaults

# ----------------------------------------------------
# Targets
# ----------------------------------------------------

ifeq ($(TCL_TAR),)
debug opt:
else
debug opt:
	gzip -dc $(TCL_TAR) | (cd ../priv && tar -xf -)
endif

clean:

docs:

# ----------------------------------------------------
# Release Target
# ---------------------------------------------------- 
include $(ERL_TOP)/make/otp_release_targets.mk

release_spec:
	$(INSTALL_DIR) $(RELSYSDIR)/priv
	$(INSTALL_DATA) $(TCL_FILES) $(EXTRA_FILES) $(RELSYSDIR)/priv
ifneq ($(TCL_TAR),)
	gzip -dc $(TCL_TAR) | (cd $(RELSYSDIR)/priv && tar -xf -)
endif

release_docs_spec:
