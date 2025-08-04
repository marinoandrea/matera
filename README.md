# Matera

> [!WARNING]
> This project is a work in progress.

`matera` is a Rust library that implements reactive Petri nets as defined by [Eshuis et al. in 2003](https://doi.org/10.1007/3-540-44919-1_20).

It is designed with reactive workflow modelling in mind, and optimised for step-wise simulation speed (as opposed to memory).

Feature overview and roadmap:

- [x] incidence matrix and marking array base implementation
- [x] full-duplex event queue for environment interaction
- [x] ~~asynchronous support~~ using `mpsc::channel` for now
- [ ] SIMD optimization based on `TRange` types
  - [x] support for `neon`
  - [ ] support for `avx512f`
  - [ ] support for `avx2`
  - [ ] support for `sse2`

The name of this library is a very dumb pun on the word _Petri_, which sounds like the italian _pietra_ meaning stone or rock.
Matera is a beautiful city in southern Italy known for its stone-carved _"sassi"_ districts.
