use bn254::*;

fn main() {
    // G1 generator (1, 2) in Montgomery form
    let p_x = Fp([0xd35d438dc58f0d9d, 0x0a78eb28f5c70b3d, 0x666ea36f7879462c, 0x0e0a77c19a07df2f]);
    let p_y = Fp([0xa6ba871b8b1e1b3a, 0x14f1d651eb8e167b, 0xccdd46def0f28c58, 0x1c14ef83340fbe5e]);

    // G2 generator in Montgomery form: x = (x0, x1), y = (y0, y1)
    let q_x = Fp2 {
        c0: Fp([0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b]),
        c1: Fp([0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]),
    };
    let q_y = Fp2 {
        c0: Fp([0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206]),
        c1: Fp([0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]),
    };

    let mut result = Fp12::zero();
    pairing(&mut result, &p_x, &p_y, &q_x, &q_y);

    println!("e(G1, G2).c0.c0.c0 = {:?}", result.c0.c0.c0.0);

    // Expected c0 in Montgomery form:
    // [0x53e1d9fc3a8329ef, 0x9254a1949ff5465f, 0x3d01af561fad5084, 0x2ae045056b3b7c1e]
    let expected_c0 = Fp([0x53e1d9fc3a8329ef, 0x9254a1949ff5465f, 0x3d01af561fad5084, 0x2ae045056b3b7c1e]);
    if result.c0.c0.c0 == expected_c0 {
        println!("PASS: pairing matches py_ecc test vector!");
    } else {
        println!("MISMATCH: expected {:?}", expected_c0.0);
        println!("          got      {:?}", result.c0.c0.c0.0);
    }
}
