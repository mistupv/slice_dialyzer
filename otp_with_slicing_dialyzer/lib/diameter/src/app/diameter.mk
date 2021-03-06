#-*-makefile-*-   ; force emacs to enter makefile-mode

# %CopyrightBegin%
#
# Copyright Ericsson AB 2010-2011. All Rights Reserved.
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

DIAMETER_TOP = /home/kostis/slice/otp_src_R14B04+slice/lib/diameter

# ifneq ($(PREFIX),)
# ifeq ($(TESTROOT),)
# TESTROOT = $(PREFIX)
# endif
# endif

ifeq ($(USE_DIAMETER_TEST_CODE), true)
ERL_COMPILE_FLAGS += -DDIAMETER_TEST_CODE=mona_lisa_spelar_doom
endif

ifeq ($(USE_DIAMETER_HIPE), true)
ERL_COMPILE_FLAGS += +native
endif

ifeq ($(WARN_UNUSED_WARS), true)
ERL_COMPILE_FLAGS += +warn_unused_vars
endif

DIAMETER_APP_VSN_COMPILE_FLAGS = \
	+'{parse_transform,sys_pre_attributes}' \
	+'{attribute,insert,app_vsn,$(APP_VSN)}'

DIAMETER_ERL_COMPILE_FLAGS += \
	-pa $(DIAMETER_TOP)/ebin  \
	$(DIAMETER_APP_VSN_COMPILE_FLAGS) 

