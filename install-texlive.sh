#!/bin/bash

# Put the current working directory into the profile file
sed 's@PWD@'"$PWD"'@' < texlive.profile > texlive.localized.profile

# Get the TexLive installer
wget http://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz
tar zvxf install-tl-unx.tar.gz
cd `ls -d install-tl-[0-9]*`
./install-tl --profile ../texlive.localized.profile
cd ..

# Now install the required packages into our fresh installation
export PATH=$PWD/texlive/bin/x86_64-linux:$PATH
tlmgr install \
 afterpage \
 amsfonts \
 amsmath \
 amssymb \
 amsthm \
 bm \
 bussproofs \
 cancel \
 color \
 color \
 courier \
 enumerate \
 fancyhdr
 fix-cm \
 float \
 geometry \
 hyperref \
 interval \
 lastpage \
 libertine \
 listings \
 makeidx \
 mdframed \
 minted \
 newtxmath \
 nicefrac \
 proof \
 todonotes \
 verbatim
