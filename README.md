## Overview

This is an implementation of `Photon` and `Quark` using `OCaml`. When executed, the hash value and processing time are displayed on the console.

## Description

Photon used the parameters `PHOTON-80/20/16`, `PHOTON-224/32/32`, and `PHOTON-256/32/32`. Quark used the parameters `U-Quark`, `D-Quark`, and `S-Quark`. All parameters in Photon and Quark are implemented using the `Array`, `List`, and `Binary tree` data structures, respectively. In addition, Quark implements a speedup by retrieving the values before processing (`Pre`).

The combinations of parameters and data structures are as follows:

| | `Array` | `List` | `Binary tree` | `Pre (List)` | `Pre (Binary tree)` |
| --- | --- | --- | --- | --- | --- |
| `PHOTON-80/20/16` | [photon80](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/photon80.ml) | [photon80_list](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/list/photon80_list.ml) | [photon80_bt](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/bt/photon80_binarytree.ml) | - | - |
| `PHOTON-224/32/32` | [photon224](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/photon224.ml) | [photon224_list](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/list/photon224_list.ml) | [photon224_bt](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/bt/photon224_binarytree.ml) | - | - |
| `PHOTON-256/32/32` | [photon256](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/photon256.ml) | [photon256_list](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/list/photon256_list.ml) | [photon256_bt](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/photon/bt/photon256_binarytree.ml) | - | - |
| `U-Quark` | [u_quark](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/u_quark.ml) | [u_quark_list](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/list/u_quark_list.ml) | [u_quark_bt](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/bt/u_quark_binarytree.ml) | [u_quark_list_pre](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/list/pre/u_quark_list_pre_get.ml) | [u_quark_bt_pre](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/bt/pre/u_quark_binarytree_pre_get.ml) |
| `D-Quark` | [d_quark](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/d_quark.ml) | [d_quark_list](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/list/d_quark_list.ml) | [d_quark_bt](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/bt/d_quark_binarytree.ml) | [d_quark_list_pre](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/list/pre/d_quark_list_pre_get.ml) | [d_quark_bt_pre](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/bt/pre/d_quark_binarytree_pre_get.ml) |
| `S-Quark` | [s_quark](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/s_quark.ml) | [s_quark_list](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/list/s_quark_list.ml) | [s_quark_bt](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/bt/s_quark_binarytree.ml) | [s_quark_list_pre](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/list/pre/s_quark_list_pre_get.ml) | [s_quark_bt_pre](https://github.com/kwdlab/minoda.shu/blob/kuwakado.hidenori/quark/bt/pre/s_quark_binarytree_pre_get.ml) |

## Requirement

- OCaml 4.13.0+

## Usage

### Photon

```
main_photon [-p80] [-p224] [-p256]
```

#### Example
```sh
$ ocamlopt -o main_photon photon80.ml photon224.ml photon256.ml main_photon.ml

$ ./main_photon -p80
```

### Quark

```
main_quark [-u] [-d] [-s]
```

#### Example

```sh
$ ocamlopt -o main_quark u_quark.ml d_quark.ml s_quark.ml main_quark.ml

$ ./main_quark -u
```

## Install

```sh
$ git clone https://github.com/kwdlab/minoda.shu.git
```

## References

- [Photon](https://sites.google.com/site/photonhashfunction/home)
- [Quark](https://www.aumasson.jp/quark/)

## Author

- [Shu Minoda](https://github.com/papannda444)

## License

- [MIT](https://opensource.org/licenses/MIT)
