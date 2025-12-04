package src


final class lib$_ {
def args = lib_sc.args$
def scriptPath = """src/lib.sc"""
/*<script>*/
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
def quicksort(input: ZS, start: Z, stop: Z): Unit = {
  Contract(
    Requires(
      start >= 0,
      stop >= 0,
      stop >= start,
      stop < input.size
    ),
    Modifies(input),
    Ensures(
      ∀(start + 1 to stop)(i __>: (input(i) > input(i - 1))),
      input.size == In(input).size
    )
  )

  val length = stop - start
  if (length <= 1) {
    return
  }

  val pivot: Z = input(stop)
  var index = start
  var pointer = start
  while (pointer < stop) {
    Invariant(
      Modifies(
        index,
        pointer,
        input
      ),
      ∀(start until pointer)(i __>: (input(i) < pivot)),
      index <= pointer,
      index >= 0,
      index < input.size,
      pointer >= 0,
      pointer < input.size,
      input.size == In(input).size
    )
    if (input[pointer] < pivot) {
      swap(input, pointer, index)
      index += 1
    }
    pointer += 1
  }

  swap(index, index, pointer)

  quicksort(input, start, index)
  quicksort(input, index + 1, stop)
}

def quicksort(input: ZS): Unit = {
  Contract(
    Modifies(
      input
    ),
    Ensures(
      ∀(0 until index.size)(i __>: (input(i) > input(i - 1))),
      input.size == In(input).size
    )
  )

  if (input.size <= 1) {
    return
  }

  quicksort(input, 0, input.size - 1)
}

// ---TESTS---

// empty
var empty = Sequence()
quicksort(empty)
assert(empty, Sequence())

// one element

// two

// three

// four

// 8

// 16

// 32

// 42

// 49

/*</script>*/ /*<generated>*//*</generated>*/
}

object lib_sc {
  private var args$opt0 = Option.empty[Array[String]]
  def args$set(args: Array[String]): Unit = {
    args$opt0 = Some(args)
  }
  def args$opt: Option[Array[String]] = args$opt0
  def args$: Array[String] = args$opt.getOrElse {
    sys.error("No arguments passed to this script")
  }

  lazy val script = new lib$_

  def main(args: Array[String]): Unit = {
    args$set(args)
    val _ = script.hashCode() // hashCode to clear scalac warning about pure expression in statement position
  }
}

export lib_sc.script as `lib`

