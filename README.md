# Sorticoq

A small collection of Coq-verified sorting algorithms over ordered types.

### Definitions

In that repo sorting algorithms are represented as functions which are to imitate well-known imperative realisations from Wikipedia.

In that repo a sorting algorithm is correct if it satisfies the following conditions:
* The output is a permutation of the input
* The output is sorted

### What do we have there?

* src/InsertionSort
* src/SelectionSort
* src/TreeSort
* src/QuickSort -- tried to imitate Lomouto's QuickSort (where a pivot is the first element of a list)
* src/BubbleSort
