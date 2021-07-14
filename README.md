# AUCurves - High Assurance Cryptography by means of code synthesis.
In this project we aim to develop frameworks for synthesizing formally verified implementations of cryptographic primitives.
At the moment we are able to produce implementations of groups G1 and G2 of the elliptic curve(s) BLS12-381, as well as the quadratic field extension arithmetic underlying G2.

**Our approach**
We expand on the infrastructure provided by the Fiat-Crypto and Bedrock2 projects, upon which this project depends.
We use the base field arithmetic synthesized by Fiat-Crypto as (as of yet) atomic building blocks in our implementations, and use Bedrock2's "ExprImp" as an intermediate language that allows us to proof correctness of our implementations, while abstracting over a number of parameters such as prime modulos, system bitwidth and curve-defining parameters.

**How to build**
Cloning this repo with the "--recursive" flag will ensure that the necessary dependencies are downloaded as well.
Note that fiat-crypto, when installed through OPAM, may not include the Bedrock2 backend. If you plan to install fiat-crypto through OPAM, this backend must be installed manually, e.g. by running
    make
from the source folder of fiat-crypto.

**Visions**
As the project matures, we aim to develop verified implementations of pairing computations, as well as addressing performance issues that currently exist.
We will also be targeting Rust, and verify our implementations against hacspec specifications.