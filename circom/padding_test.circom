
/*
  We wish to test padding for an R1CS with the following characteristics:
  - Original instance length: 5 -> Padded to 8
  - Original witness length: 3
  - Smallest power of 2 geq 8 + 3: 16
  - Original number of constraints: 7 -> 16
*/

template PaddingTest() {

    // Public
    signal input a1;
    signal input a2;
    signal input b1;
    signal input b2;

    // Private
    signal input c;
    signal a2c;

    a2 === a1 * a1;
    b2 === b1 * b1;

    a2c <== a2 * c;
    42 === b2 * a2c;
}

component main {public [a1, a2, b1, b2]} = PaddingTest();
