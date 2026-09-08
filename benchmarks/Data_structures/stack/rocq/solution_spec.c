/*@ Extern Coq (sll :: *) */
/*@ Extern Coq
      (stack_capacity : Z)
      (sll_empty : sll)
      (sll_cons : Z -> sll -> sll)
      (sll_from_array : list Z -> sll)
      (store_stack : Z -> sll -> Z -> Assertion)
      (BuildStackPrefix : sll -> list Z -> Z -> Prop)
      (StackConcreteView : sll -> list Z -> Z -> Prop)
 */
/*@ Import Coq Require Import PVbench.Data_structures.stack.rocq.spec_lib */

void push(int *stack, int n, int x)
/*@ With (before : sll)
    Require
      n < stack_capacity &&
      store_stack(stack, before, n) *
      IntArray::undef_seg(stack, n, n + 1)
    Ensure
      store_stack(stack, sll_cons(x, before), n + 1)
 */
{

  stack[n] = x;

}

int pop(int *stack, int n)
/*@ With (top : Z) (rest : sll)
    Require
      1 <= n &&
      store_stack(stack, sll_cons(top, rest), n)
    Ensure
      __return == top &&
      store_stack(stack, rest, n - 1) *
      IntArray::undef_seg(stack, n - 1, n)
 */
{

  int ret = stack[n - 1];

  return ret;
}

void build(int *stack, int n)
/*@ With (input : list Z)
    Require
      0 <= n &&
      n <= stack_capacity &&
      Zlength(input) == n &&
      IntArray::full(stack, n, input)
    Ensure
      store_stack(stack, sll_from_array(input), n)
 */
{

  for (int i = 1; i < n; ++i) {
    int x = stack[i];

    push(stack, i, x);

  }

}

