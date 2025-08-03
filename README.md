# Matera

> ![warning]
> This project is a work in progress.

This library implements reactive Petri nets following the definition by [Eshuis et al.
published in 2003](https://doi.org/10.1007/3-540-44919-1_20).

Reactive Petri nets differ from normal ones because they can interact with an
external system. Therefore, the token-game semantics are modified to account
for asynchronous interactions with an environment that the net is monitoring.

To achieve this, the net distinguishes between _internal_ and _external_ transitions.
We call a net _stable_ if all its internal transitions are disabled, _unstable_
otherwise. Moreover, we assume the _Perfect Synchrony Hypothesis_, which states that
internal transitions are always faster that external ones. Based on these definitions,
the net operates in two different modes: it either executes internal transitions until
it reaches stability, or it executes external ones one at a time.

The net is implemented using an incidence matrix and marking array approach.
While each node (place or transition) is labeled with a string name, they
are internally mapped to integer indices. In the marking array T, for each
place i we have:

    T[i] = tokens_i

This also allows us to build an incidence matrix W with size NxM (where N = # of transitions
and M = # of places). Therefore, given a transition x and place y:

    W[x][y] = weight_arc_xy

We represent input arcs with negative weights so they consume tokens, and
output arcs with positive weights so they produce tokens. With this premise,
firing a complete transition x is equivalent to the following operation:

    T = T + W[x]

External transitions are fired in two steps, first tokens are consumed and events are
pushed to the environment. Then, once the completion event is received, tokens are
produced in the ouput arcs.
