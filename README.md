Description
--

This repository contains Magma code for determining the stable reduction type of a quartic.
The latter code works over number fields, including rationals (see [Bom+23b]).

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

The function `QuarticTypeFromOctad(f, p)` is the main function provided by this package. As input to a plane quartic curve `f`, it returns its stable reduction type modulo the prime number `p` (assumed to be greater than 2). In general, there are 74 possible types of stable reductions for a singular quartic: 42 of general type and 32 of hyperelliptic type.

For example, the following script returns `(0eee)`, which means that modulo 3 the stable reduction of the curve consists of 3 elliptic curves all three secant to a curve of genus 0.
```
        _<x,y,z> := PolynomialRing(Rationals(), 3);

        f := 54*x^4 + 18*x^3*y + 18*x^3*z + 2*x^2*y^2 + 2*x^2*y*z + 8*x^2*z^2 + 18*x*y^3 +
        2*x*y^2*z + 8*x*y*z^2 + 18*x*z^3 + 54*y^4 + 18*y^3*z + 8*y^2*z^2 + 18*y*z^3 + 54*z^4;

        QuarticTypeFromOctad(f, 3);
```

The reduction modulo 7 of same curve  is a quartic with 2 nodes, i.e a curve of geometric genus 1 (type `(1nn)`), and modulo 37 a quartic with a single node, i.e a a curve of geometric genus 2 (type `(2n)`).
```
        QuarticTypeFromOctad(f,  7);

        QuarticTypeFromOctad(f, 37);
```

Of independent interest, the function `QuarticByReductionType(type, p)` (resp. `G3HyperReductionType(type, p)` with `G3QuarticFromHyper(h, p^2)`) returns a quartic of the type given in input, among the 42 possible ones (resp. among the 32 possible hyperelliptic ones).

Examples are given in the directory [`examples`](examples). A full list of intrinsics is [here](intrinsics.md).

Verbose comments are enabled by
```
        SetVerbose("G3Cayley", n);
```
where `n` is either `0`, `1` or `2`. A higher value gives more comments.


Citing this code
--

Please cite the following preprint if this code has been helpful in your research:

[Bom+23] Raymond van Bommel, Jordan Docking, Vladimir Dokchitser, Reynald Lercier and Elisa Lorenzo García,
*Reduction of plane quartics and Cayley octads*,
[arXiv:2102.04372](https://arxiv.org/abs/2102.04372).
