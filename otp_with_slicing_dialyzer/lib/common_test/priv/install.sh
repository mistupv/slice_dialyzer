#!/bin/sh

CT_ROOT=$1
CT_VSN=1.5.5
TS_VSN=3.4.5

if [ -z "$CT_ROOT" ]
then
    echo "install.sh: need CT_ROOT (absolute) directory or 'local' as argument"
    exit 1
fi

if [ $CT_ROOT = "local" ]
then
    CT_DIR=`pwd`
    cd priv
    sed -e "s,@CTPATH@,$CT_DIR/ebin," \
        -e "s,@TSPATH@,$CT_DIR/../test_server/ebin," \
	run_test.in > bin/run_test
    chmod 775 bin/run_test
    echo "install successful, start script created in " $CT_ROOT/common_test-$CT_VSN/priv/bin
else

    if [ ! -d "$CT_ROOT" ]
    then
	echo "install.sh: CT_ROOT argument must be a valid directory"
	exit 1
    fi

    if [ `echo $CT_ROOT | awk '{ print substr($1,1,1) }'` != "/" ]
    then
	echo "install.sh: need an absolute path to CT_ROOT"
	exit 1
    fi

    if [ ! -d $CT_ROOT/common_test-$CT_VSN ]
    then
	echo "install.sh: The directory $CT_ROOT/common_test-$CT_VSN does not exist"
	exit 1
    fi

    if [ -d $CT_ROOT/common_test-$CT_VSN/priv ]
    then
	cd $CT_ROOT/common_test-$CT_VSN/priv
	sed -e "s;@CTPATH@;$CT_ROOT/common_test-$CT_VSN/ebin;" \
	    -e "s;@TSPATH@;$CT_ROOT/test_server-$TS_VSN/ebin;" \
	    run_test.in > bin/run_test
	chmod 775 bin/run_test
	echo "install successful, start script created in " $CT_ROOT/common_test-$CT_VSN/priv/bin
    fi
fi


