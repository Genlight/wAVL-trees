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

# LiquidHaskell

I installed it via the source, from github. Clone it + the submodules and run `stack install`. Then 

# Environment

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

