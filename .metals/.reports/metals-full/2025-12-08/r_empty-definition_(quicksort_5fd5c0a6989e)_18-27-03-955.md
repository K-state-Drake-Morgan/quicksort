file://<WORKSPACE>/src/lib.sc
empty definition using pc, found symbol in pc: 
semanticdb not found
empty definition using fallback
non-local guesses:
	 -org/sireum/int.
	 -org/sireum/int#
	 -org/sireum/int().
	 -int.
	 -int#
	 -int().
	 -scala/Predef.int.
	 -scala/Predef.int#
	 -scala/Predef.int().
offset: 708
uri: file://<WORKSPACE>/src/lib.sc
text:
```scala
// #Sireum #Logika

import org.sireum._

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
def quicksort_part(input: ZS, start: Z, stop: Z): Unit = {
  if (len <= 1)
            {
                return;
            }
            in@@t segmentL = start;
            int segmentE = start + len - 1;
            int segmentG = start + len - 1;
            int pivot = list[start];
            while (segmentL <= segmentE)
            {
                if (list[segmentE] < pivot)
                { // Seg L
                    Swap(list, segmentE, segmentL );
                    segmentL++;
                } else if (list[segmentE] == pivot )
                { // Seg E
                    segmentE--;
                } else
                { // Seg G
                    Swap(list, segmentE, segmentG);
                    segmentG--;
                    segmentE--;
                }
            }
            //Swap(list, len - 1, segmentE);
            QuickSort(list, start, segmentL - start);
            QuickSort(list, segmentG + 1, start + len - segmentG - 1);
}

def quicksort(input: ZS): Unit = {
  Contract(
    Modifies(
      input
    ),
    Ensures(
      ∀(1 until input.size)(i => (input(i) > input(i - 1))),
      input.size == In(input).size
    )
  )

  if (input.size <= 1) {
    return
  }

  quicksort_part(input, 0, input.size )
}

// ---TESTS---

// empty
var empty = ZS()
quicksort(empty)
assert(empty == ZS())

// one element
var one = ZS(1)
quicksort(one)
assert(one == ZS(1))

// two
var two = ZS(2,1)
quicksort(two)
assert(two == ZS(1,2))

// three
var three = ZS(3,1,2)
quicksort(three)
assert(three == ZS(1,2,3))

// four
var four = ZS(4,3,1,2)
quicksort(four)
assert(four == ZS(1,2,3,4))

// 8
var eight = ZS(8,3,7,1,6,2,5,4)
quicksort(eight)
assert(eight == ZS(1,2,3,4,5,6,7,8))

// 16
var sixteen = ZS(16,5,12,1,9,3,15,2,8,7,14,6,4,11,10,13)
quicksort(sixteen)
assert(sixteen == ZS(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16))

// 32
var thirtytwo = ZS(
  32,17,5,29,1,14,8,23,
  11,3,27,19,7,25,13,9,
  2,30,6,22,12,4,26,18,
  15,10,31,16,24,20,28,21
)
quicksort(thirtytwo)
assert(thirtytwo ==
  ZS(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
     17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32)
)

// 42
var fortytwo = ZS(
  42,21,5,38,9,1,17,33,12,7,25,40,3,29,
  18,6,31,10,36,4,22,14,34,8,28,15,19,11,
  41,2,35,13,30,20,39,16,23,37,24,32,26
)
quicksort(fortytwo)
assert(fortytwo ==
  ZS(
    1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
    22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,
    40,41,42
  )
)

// 49
var fortynine = ZS(
  49,1,25,13,37,5,41,7,29,17,9,45,3,33,21,11,
  27,19,39,15,23,31,43,35,47,2,26,14,38,6,42,8,
  30,18,10,46,4,34,22,12,28,20,40,16,24,32,36,44,48
)
quicksort(fortynine)
assert(fortynine ==
  ZS(
    1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
    21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,
    37,38,39,40,41,42,43,44,45,46,47,48,49
  )
)

```


#### Short summary: 

empty definition using pc, found symbol in pc: 