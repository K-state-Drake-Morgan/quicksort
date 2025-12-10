// #Sireum #Logika

import org.sireum._

def is_sorted(input: ZS): B = {
  Contract (
    Ensures (
      Res[B] == true __>: ∀(0 until input.size - 1)(i => input(i) < input(i + 1)),
      Res[B] == false __>: !(∀(0 until input.size - 1)(i => input(i) < input(i + 1))),
    )
  )

  var index: Z = 0;
  while (index < input.size - 1) {
    Invariant (
      Modifies (
        index
      ),
      ∀(0 until index - 1)(i => (i >= 0 && i + 1 < input.size) __>: input(i) < input(i + 1))
    )
    if (input(index) > input(index + 1)) {
      return false;
    }
    index = index + 1;
  }
  return true;
}

def swap(nums: ZS, pos1: Z, pos2: Z): Unit = {
  // how to write?
  Contract(
    Requires(pos1 >= 0, pos1 < nums.size, pos2 >= 0, pos2 < nums.size),
    Modifies(nums),
    Ensures(
      nums(pos1) == In(nums)(pos2),
      nums(pos2) == In(nums)(pos1),
      ∀(0 until nums.size)(k =>
        k != pos1 & k != pos2 __>: (nums(k) == In(nums)(k))
      ),
      nums.size == In(nums).size
    )
  )

  // how to write contract?

  var temp: Z = nums(pos1)
  nums(pos1) = nums(pos2)
  nums(pos2) = temp
}

// stop is inclusive
def quicksort_part(input: ZS, start: Z, len: Z): Unit = {
  Contract (
    Requires (
      start >= 0,
      start + len <= input.size
    ),
    Modifies (
      input
    ),
    Ensures (
      ∀(start until start + len - 1)(i => input(i) <= input(i + 1))
    )
  )
  if (len <= 1)
  {
      return;
  }
  var segmentL: Z = start;
  var segmentE: Z = start + len - 1;
  var segmentG: Z = start + len - 1;
  var pivot: Z = input(start);
  while (segmentL <= segmentE)
  {
    Invariant (

      Modifies (
        input,
        segmentG,
        segmentE,
        segmentL
      ),
        segmentL >= start,
        segmentE >= start,
        segmentG >= start,
        segmentE < input.size,
        segmentG < input.size,
        segmentL < input.size,
        segmentG <= start + len - 1,
        segmentE <= start + len - 1,
        ∀(segmentE until start + len - 1) (i => i < input.size && input(i) >= pivot)
    )
      if (input(segmentE) < pivot)
      { // Seg L
          swap(input, segmentE, segmentL );
          segmentL = segmentL + 1;
      } else if (input(segmentE) == pivot )
      { // Seg E
          segmentE = segmentE - 1;
      } else
      { // Seg G
          swap(input, segmentE, segmentG);
          segmentG = segmentG - 1;
          segmentE = segmentE - 1;
      }
  }
  //Swap(list, len - 1, segmentE);
  quicksort_part(input, start, segmentL - start);
  quicksort_part(input, segmentG + 1, start + len - segmentG - 1);
}

def quicksort(input: ZS): Unit = {
  Contract(
    Modifies(
      input
    ),
    Ensures(
      ∀(0 until input.size - 1)(i => input(i) <= input(i + 1)),
      input.size == In(input).size
    )

  )

  if (input.size > 1) {
    quicksort_part(input, 0, input.size)
  }
}

// ---TESTS---

// empty
var empty = ZS()
quicksort(empty)
assert(empty == ZS())

// one element
var one = ZS(1)
quicksort(one)
assert(is_sorted(one))

// two
var two = ZS(2,1)
quicksort(two)
assert(is_sorted(two))

// three
var three = ZS(3,1,2)
quicksort(three)
assert(is_sorted(three))

// four
var four = ZS(4,3,1,2)
quicksort(four)
assert(is_sorted(four))

// 8
var eight = ZS(8,3,7,1,6,2,5,4)
quicksort(eight)
assert(is_sorted(eight))

// 16
var sixteen = ZS(16,5,12,1,9,3,15,2,8,7,14,6,4,11,10,13)
quicksort(sixteen)
assert(is_sorted(sixteen))

// 32
var thirtytwo = ZS(
  32,17,5,29,1,14,8,23,
  11,3,27,19,7,25,13,9,
  2,30,6,22,12,4,26,18,
  15,10,31,16,24,20,28,21
)
quicksort(thirtytwo)
assert(is_sorted(thirtytwo))

// 42
var fortytwo = ZS(
  42,21,5,38,9,1,17,33,12,7,25,40,3,29,
  18,6,31,10,36,4,22,14,34,8,28,15,19,11,
  41,2,35,13,30,20,39,16,23,37,24,32,26
)
quicksort(fortytwo)
assert(is_sorted(fortytwo))

// 49
var fortynine = ZS(
  49,1,25,13,37,5,41,7,29,17,9,45,3,33,21,11,
  27,19,39,15,23,31,43,35,47,2,26,14,38,6,42,8,
  30,18,10,46,4,34,22,12,28,20,40,16,24,32,36,44,48
)
quicksort(fortynine)
assert(is_sorted(fortynine))