|_  a=manx
:: whitelisted
::
::   check all tags are in whitelist
::
++  whitelisted
  |=  b=(set mane)
  ^-  ?
  %-  post-fold
  |=  [g=marx w=?]
  ?:  ?=(%.n w)  w
  (~(has in b) n.g)
:: whitelisted
::
::   check whether any tags are in blacklist
::
++  blacklisted
  |=  b=(set mane)
  ^-  ?
  %-  post-fold
  |=  [g=marx w=_|]
  ?:  ?=(%.y w)  w
  (~(has in b) n.g)
:: get-max-depth
::
::   deepest node depth (root is 0)
::
++  get-max-depth
  ^-  @ud
  |-
  ?~  c.a  0
  %+  max
    .+  $(c.a c.i.c.a)
  $(c.a t.c.a)
:: apply-elem:
::
::   apply gate to tags/attrs (turn for manxes)
::
++  apply-elem
  |=  b=$-(marx marx)
  |^  ^-  manx
  [(b g.a) (cloop c.a)]
  ++  cloop
    |=  c=marl
    ?~  c  ~
    [^$(a i.c) (cloop t.c)]
  --
:: apply-elem-chain
::
::   apply gate to tags/attrs with parentage given
::
::   gate takes [a b] where a is the current marx
::   and b is the list of parent marxes in ascending
::   order (i is the direct parent)
::
++  apply-elem-chain
  =/  ch=(lest marx)  ~[g.a]
  |=  b=$-([marx (list marx)] marx)
  |^  ^-  manx
  [(b ch) (cloop c.a)]
  ++  cloop
    |=  c=marl
    ?~  c  ~
    [^$(a i.c, ch [g.i.c ch]) (cloop t.c)]
  --
:: apply-nodes
::
::   apply gate to nodes in postorder
::
::   (unlike apply-elem, the gate takes the
::   whole manx instead of just marx)
::
++  apply-nodes
  |=  b=$-(manx manx)
  |^  ^-  manx
  (b [g.a (cloop c.a)])
  ++  cloop
    |=  c=marl
    ?~  c  ~
    [^$(a i.c) (cloop t.c)]
  --
:: apply-attrs
::
::   apply a gate to all attributes
::
++  apply-attrs
  |=  b=$-([mane tape] [mane tape])
  ^-  manx
  %-  apply-elem
  |=  x=marx
  =|  y=mart
  |-
  ?~  a.x  x(a (flop y))
  $(a.x t.a.x, y [(b i.a.x) y])
:: apply-text
::
::   apply a gate to all ordinary text
::
++  apply-text
  |=  b=$-(tape tape)
  ^-  manx
  %-  apply-elem
  |=  x=marx
  ?.  ?=(%$ n.x)            x
  ?~  a.x                   x
  ?.  ?=(%$ n.i.a.x)        x
  ?^  t.a.x                 x
  =.  v.i.a.x  (b v.i.a.x)  x
:: post-fold
::
::   fold over tags/attrs in postorder
::
++  post-fold
  |*  b=_|=([marx *] +<+)
  ^+  ,.+<+.b
  |-
  ?~  c.a  (b g.a +<+.b)
  $(a a(c t.c.a), +<+.b $(a i.c.a))
:: pre-fold
::
::   fold over tags/attrs in preorder
::
++  pre-fold
  |*  b=_|=([marx *] +<+)
  ^+  ,.+<+.b
  |-
  ?~  c.a
    ?:  =(%$^%$ n.g.a)
      +<+.b
    (b g.a +<+.b)
  %=    $
    a  [[%$^%$ ~] t.c.a]
      +<+.b
    %=    $
      a  i.c.a
        +<+.b
      ?:  =(%$^%$ n.g.a)
        +<+.b
      (b g.a +<+.b)
    ==
  ==
:: lvl-fold
::
::   fold over tags/attrs in level order
::
++  lvl-fold
  |*  b=_|=([marx *] +<+)
  |^  ^+  ,.+<+.b
  =.  +<+.b  (b g.a +<+.b)
  (cloop-a c.a +<+.b)
  ++  cloop-a
    |=  [c=marl acc=_+<+.b]
    =/  l  c
    |-
    ?~  l  (cloop-b c acc)
    $(l t.l, acc (b g.i.l acc))
  ++  cloop-b
    |=  [c=marl acc=_+<+.b]
    ?~  c  acc
    $(c t.c, acc (cloop-a c.i.c acc))
  --
:: prune
::
::   delete nodes when applied gate produces %.y
::
++  prune
  |=  b=$-(manx ?)
  |^  ^-  (unit manx)
  ?:  (b a)  ~
  [~ g.a (cloop c.a)]
  ++  cloop
    =|  fro=marl
    |=  to=marl
    ?~  to  (flop fro)
    =+  u=^$(a i.to)
    ?~  u  $(to t.to)
    $(to t.to, fro [u.u fro])
  --
:: prune-tag
::
::   delete nodes by tag
::
++  prune-tag
  |=  b=mane
  ^-  (unit manx)
  (prune |=(x=manx =(b n.g.x)))
::
:: prune-tags
::
::   delete nodes by tags
::
++  prune-tags
  |=  b=(set mane)
  ^-  (unit manx)
  (prune |=(x=manx (~(has in b) n.g.x)))
:: prune-namespace
::
::   delete nodes by tag namespace
::
++  prune-namespace
  |=  b=@tas
  ^-  (unit manx)
  (prune |=(x=manx ?@(n.g.x %.n =(b -.n.g.x))))
:: prune-namespaces
::
::   delete nodes by tag namespaces
::
++  prune-namespaces
  |=  b=(set @tas)
  ^-  (unit manx)
  (prune |=(x=manx ?@(n.g.x %.n (~(has in b) -.n.g.x))))
:: prune-attr
::
::   delete nodes by attribute name
::
++  prune-attr
  |=  b=mane
  ^-  (unit manx)
  %-  prune
  |=  x=manx
  %+  roll  a.g.x
  |=  [[n=mane v=tape] w=_|]
  ?:(w w =(n b))
:: prune-attrs
::
::   delete nodes by attribute names
::
++  prune-attrs
  |=  b=(set mane)
  ^-  (unit manx)
  %-  prune
  |=  x=manx
  %+  roll  a.g.x
  |=  [[n=mane v=tape] w=_|]
  ?:  w  w
  (~(has in b) n)
:: prune-depth
::
::   delete nodes deeper than b (root is 0)
::
++  prune-depth
  |=  b=@ud
  |^  ^-  (unit manx)
  ?:  =(0 b)  ~
  [~ g.a (cloop c.a)]
  ++  cloop
    |=  to=marl
    =|  fro=marl
    |-
    ?~  to  (flop fro)
    =/  x   (prune-depth(a i.to) (dec b))
    ?~  x   $(to t.to)
    $(to t.to, fro [u.x fro])
  --
:: del-attrs
::
::   delete attributes by name
::
++  del-attrs
  |=  b=(set mane)
  ^-  manx
  %-  apply-elem
  |=  x=marx
  =|  y=mart
  |-
  ?~  a.x  x(a (flop y))
  ?:  (~(has in b) n.i.a.x)
    $(a.x t.a.x)
  $(a.x t.a.x, y [i.a.x y])
:: keep-attrs
::
::   delete all attributes except those
::   with the given names
::
++  keep-attrs
  |=  b=(set mane)
  ^-  manx
  %-  apply-elem
  |=  x=marx
  =|  y=mart
  |-
  ?~  a.x  x(a (flop y))
  ?.  (~(has in b) n.i.a.x)
    $(a.x t.a.x)
  $(a.x t.a.x, y [i.a.x y])
:: post-flatten
::
::   get a list of elements by postorder traversal
::
++  post-flatten
  ^-  marl
  (flop (post-fold |=([x=marx l=marl] [[x ~] l])))
:: pre-flatten
::
::   get a list of elements by preorder traversal
::
++  pre-flatten
  ^-  marl
  (flop (pre-fold |=([x=marx l=marl] [[x ~] l])))
:: lvl-flatten
::
::   get a list of elements by level order traversal
::
++  lvl-flatten
  ^-  marl
  (flop (lvl-fold |=([x=marx l=marl] [[x ~] l])))
:: post-get-text
::
::   get a list of plain text by postorder traversal
::
++  post-get-text
  ^-  wall
  %-  flop
  %-  post-fold
  |=  [x=marx l=wall]
  ?.  ?=(%$ n.x)      l
  ?~  a.x             l
  ?.  ?=(%$ n.i.a.x)  l
  ?^  t.a.x           l
  :-  v.i.a.x         l
:: pre-get-text
::
::   get a list of plain text by preorder traversal
::
++  pre-get-text
  ^-  wall
  %-  flop
  %-  pre-fold
  |=  [x=marx l=wall]
  ?.  ?=(%$ n.x)      l
  ?~  a.x             l
  ?.  ?=(%$ n.i.a.x)  l
  ?^  t.a.x           l
  :-  v.i.a.x         l
:: lvl-get-text
::
::   get a list of plain text by level order traversal
::
++  lvl-get-text
  ^-  wall
  %-  flop
  %-  lvl-fold
  |=  [x=marx l=wall]
  ?.  ?=(%$ n.x)      l
  ?~  a.x             l
  ?.  ?=(%$ n.i.a.x)  l
  ?^  t.a.x           l
  :-  v.i.a.x         l
:: search-text
::
:: find plain text containing the given cord
::
++  search-text
  |=  b=@t
  ^-  wall
  %-  flop
  %-  post-fold
  |=  [x=marx l=wall]
  ?.  ?=(%$ n.x)      l
  ?~  a.x             l
  ?.  ?=(%$ n.i.a.x)  l
  ?^  t.a.x           l
  =+  par=(cury (jest b) *hair)
  ?.  |-
      ?~  v.i.a.x  %.n
      ?^  (tail (par v.i.a.x))
        %.y
      $(v.i.a.x t.v.i.a.x)
    l
  [v.i.a.x l]
--
