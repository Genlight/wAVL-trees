# Environment
i started to install all of this using the following environment: 

WSL 2 under Win10, using Ubuntu LTS 20.4 

```bash 
$ ~/lhTest$ ghc --version
The Glorious Glasgow Haskell Compilation System, version 9.2.5
$ ~/lhTest$ stack --version
Version 2.9.1, Git revision 409d56031b4240221d656db09b2ba476fe6bb5b1 x86_64 hpack-0.35.0
$ ~/lhTest$ ghcup --version
The GHCup Haskell installer, version v0.1.18.0
$ ~/lhTest$ code --version
1.73.1
6261075646f055b99068d3688932416f2346dd3b
x64
```

# Install Stack
follow the guide: [https://docs.haskellstack.org/en/stable/install_and_upgrade/](https://docs.haskellstack.org/en/v1.0.2/install_and_upgrade/)

add repositories: 
```
$ sudo apt-key adv --keyserver keyserver.ubuntu.com --recv-keys 575159689BEFB442
$ echo 'deb http://download.fpcomplete.com/ubuntu focal main'|sudo tee /etc/apt/sources.list.d/fpco.list
```

and install stack: 
```
$ sudo apt install haskell-stack
```

Then, when installed, you can download the repo from Github

```bash
$ git clone git@github.com:Genlight/lhTest.git
```

and do a `stack build`. This should install all dependencies for you. Then, you should see also the LiquidHaskell checks and the output at the end, like this: 

```bash
master@Dell:~/lhTest$ stack build
lhTest> build (lib)
Preprocessing library for lhTest-0.1.0.0..
Building library for lhTest-0.1.0.0..
[1 of 1] Compiling WAVL

**** LIQUID: UNSAFE ************************************************************

/home/master/lhTest/src/WAVL.hs:197:37: error:
    Liquid Type Mismatch
...
```

# install VS code + Extensions
install VS code from [the official page](https://code.visualstudio.com/download).

I use the following extensions for my LiquidHaskell workspace: 
```bash
$ code --list-extensions
Extensions installed on WSL: Ubuntu-20.04:
dramforever.vscode-ghc-simple
haskell.haskell
justusadam.language-haskell
mustafahafidi.liquidhaskell-diagnostics
ndmitchell.haskell-ghcid
...
```

How to install extensions is explained [here](https://code.visualstudio.com/docs/editor/extension-marketplace)