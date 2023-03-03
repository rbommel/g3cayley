Description
--

This repository contains Magma code for determining the stable reduction type of a quartic.
The latter code works over number fields, including rationals.

Prerequisites
--

An installation of Magma.

Installation
--

You can enable the functionality of this package in Magma by attaching the `g3cayley/magma/spec` file with `AttachSpec`. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc` file, by adding the line
```
AttachSpec("~/Programs/g3cayley/magma/spec");
```

Usage
--

Examples are given in the directory [`examples`](examples) (a full list of intrinsics is [here](intrinsics.md)).

Verbose comments are enabled by
```
SetVerbose("G3Cayley", n);
```
where `n` is either `0`, `1` or `2`. A higher value gives more comments.


Citing this code
--

Please cite the following preprint if this code has been helpful in your research:

Raymond van Bommel, Jordan Docking, Vladimir Dokchitser, Reynald Lercier and Elisa Lorenzo García,
*Reduction of plane quartics and Cayley octads*,
[arXiv:2102.04372](https://arxiv.org/abs/2102.04372).
