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
  Contract(
    Requires(
      start >= 0,
      stop >= 0,
      stop >= start,
      stop < input.size
    ),
    Modifies(input),
    Ensures(
      ∀(start + 1 to stop)(i => (input(i) > input(i - 1))),
      input.size == In(input).size
    )
  )

  val length = stop - start
  if (length <= 1) {
    return
  }

  val pivot: Z = input(stop)
  var index: Z = start
  var pointer: Z = start
  while (pointer < stop) {
    Invariant(
      Modifies(
        index,
        pointer,
        input
      ),
      ∀(start until pointer)(i => (input(i) < pivot)),
      index <= pointer,
      index >= 0,
      index < input.size,
      pointer >= 0,
      pointer < input.size,
      input.size == In(input).size
    )
    if (input(pointer) < pivot) {
      swap(input, pointer, index)
      index = index + 1
    }
    pointer = pointer + 1
  }

  swap(input, index, pointer)

  quicksort_part(input, start, index)
  quicksort_part(input, index + 1, stop)
}

def quicksort(input: ZS): Unit = {
  Contract(
    Modifies(
      input
    ),
    Ensures(
      ∀(0 until input.size)(i => (input(i) > input(i - 1))),
      input.size == In(input).size
    )
  )

  if (input.size <= 1) {
    return
  }

  quicksort_part(input, 0, input.size - 1)
}

// ---TESTS---

// empty
var empty = ZS()
quicksort(empty)
assert(empty == ZS())

// one element

// two

// three

// four

// 8

// 16

// 32

// 42

// 49
