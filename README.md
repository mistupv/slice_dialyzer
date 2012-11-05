slice_dialyzer
==============

This version of the slicer is under development.
It works with the previous Dialyzer's version of early 2012, and it
can be used to produce slices with that Dializer version that is
distributed with the slicer.
Due to  the last changes in Dialyzer the slicer is being adapted to
the new PLT tables.


Untar the file otp_with_slicing_dialyzer.tar, then run the following commands:

./otp_build autoconf
./configure
make
./bin/dialyzer --build_plt dummy_plt.beam

After this run Dialyzer with the slicing features with:

./bin/dialyzer --slice <example_file>
