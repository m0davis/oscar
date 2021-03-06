;; This runs on OSCAR_3.31
#| To run these problems, first load Perception-Causes_3.31a.lisp.
Then load this file. To run problem n, execute (simulate-oscar n). |#

(setf *simulation-problems* nil)

;======================================================================

(make-simulation-problem
  :number  1
  :message
  "This is the perceptual updating problem.  First, Fred looks red to me.  Later, Fred looks blue to me.
What should I conclude about the color of Fred?"
  :reasons
  *PERCEPTION*
  *TEMPORAL-PROJECTION*
  *incompatible-colors*
  :inputs
  (1   "(the color of Fred is red)" 1.0)
  (30   "(the color of Fred is blue)" 1.0)
  :interests
  ("(? x)((the color of Fred is x) at 50)" 0.2)
  )

;======================================================================

(make-simulation-problem
  :number  2
  :message
  "This is the perceptual updating problem.  First, Fred looks red to me.  Later, Fred looks blue to me.
What should I conclude about the color of Fred?"
  :reasons
  *INDEXICAL-PERCEPTION*
  *indexical-incompatible-colors*
  :inputs
  (1   "(the color of Fred is red)" 1.0)
  (30   "(the color of Fred is blue)" 1.0)
  :interests
  ("(? x)(the color of Fred is x)" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  3
  :message
  "First, Fred looks red to me.  Later, I am informed by Merrill that I am then
wearing blue-tinted glasses.  Later still, Fred looks blue to me.  All along, I know that the
probability is not high of Fred being blue given that Fred looks blue to me, but I am
wearing blue tinted glasses.  What should I conclude about the color of Fred?"
  :reasons
  *PERCEPTION*
  *RELIABLE-INFORMANT*
  *PERCEPTUAL-RELIABILITY*
  *TEMPORAL-PROJECTION*
  *INCOMPATIBLE-COLORS*
  :inputs
  (1   "(the color of Fred is red)" 0.8)
  (20   "(Merrill reports that I_am_wearing_blue_tinted_glasses)" 1.0)
  (30   "(the color of Fred is blue)" 0.8)
  :premises
  ("((the probability of (the color of Fred is blue) given
    ((I have a percept with content (the color of Fred is blue)) & I_am_wearing_blue_tinted_glasses)) <= .8)"
    1.0)
  ("(Merrill is a reliable informant)" 1.0)
  :interests
  ("(? x)((the color of Fred is x) at 50)" 0.55)
  )

;======================================================================
;; This requires the temporal-projectibility of ~my_surroundings_are_illuminated_by_red_light.

(make-simulation-problem
  :number  4
  :message
  "This illustrates the use of discounted-perception and perceptual-unreliability."
  :reasons
  *perception*
  *discounted-perception*
  *perceptual-reliability*
  *perceptual-unreliability*
  *temporal-projection*
  neg-at-intro
  :inputs
  (10 "(the color of Fred is red)" 1.0)

  :premises
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red))
       & my_surroundings_are_illuminated_by_red_light)) <= .7)"
    1.0)
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red)) & I_am_wearing_red_tinted_glasses)) <= .8)"
    1.0)
  ("(I_am_wearing_red_tinted_glasses at 1)" 1.0 15)
  ("(my_surroundings_are_illuminated_by_red_light at 1)" 1.0 30)
  ("(~my_surroundings_are_illuminated_by_red_light at 8)" 1.0 50)
  :interests
  ("((the color of Fred is red) at 10)" 0.5)
  )

;======================================================================
;; This requires the temporal-projectibility of ~my_surroundings_are_illuminated_by_red_light.

(make-simulation-problem
  :number  5
  :message
  "This illustrates the use of discounted-indexical-perception and indexical-perceptual-unreliability."
  :reasons
  *indexical-perception*
  *discounted-indexical-perception*
  *indexical-perceptual-reliability*
  *indexical-perceptual-unreliability*
  *temporal-projection*
  neg-at-intro
  :inputs
  (10 "(the color of Fred is red)" 1.0)

  :premises
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red))
       & my_surroundings_are_illuminated_by_red_light)) <= .7)"
    1.0)
  ("((the probability of (the color of Fred is red) given
    ((I have a percept with content (the color of Fred is red)) & I_am_wearing_red_tinted_glasses)) <= .8)"
    1.0)
  ("(I_am_wearing_red_tinted_glasses at 1)" 1.0 15)
  ("(my_surroundings_are_illuminated_by_red_light at 1)" 1.0 30)
  ("(~my_surroundings_are_illuminated_by_red_light at 8)" 1.0 50)
  :interests
  ("(the color of Fred is red)" 0.5)
  )

;======================================================================
(make-simulation-problem
  :number  6
  :message
  "This is the Yale Shooting Problem.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired.  Should I conclude that Jones becomes dead?"
  :reasons
  neg-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER+*
  *CAUSAL-IMPLICATION*
  neg-at-intro
  :inputs
  :premises
  ("(the_gun_is_loaded at 20)" 1.0)
  ("((Jones is alive) at 20)" 1.0)
  ("(the_gun_is_fired at 30)" 1.0)
  ("(all x)(all time)(((x is dead) at time) <-> ~((x is alive) at time))" 1.0)
  ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           (Jones is dead) after an interval 10)" 1.0)
  :interests
  ("((Jones is alive) at 50)" 0.75)
  ("((Jones is dead) at 50)" 0.75)
  )

;======================================================================
(make-simulation-problem
 :number  7
 :message
  "This is the solved Yale Shooting Problem.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired.  Should I conclude that Jones becomes dead?"
  :reasons
   neg-at-elimination
   *TEMPORAL-PROJECTION*
   *CAUSAL-UNDERCUTTER*
   *CAUSAL-IMPLICATION*
   neg-at-intro
   :inputs
   :premises
   ("(the_gun_is_loaded at 20)" 1.0)
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   :interests
    ("(? ((Jones is alive) at 50))" 0.75)
   )

;======================================================================
(make-simulation-problem
 :number  13
 :message
  "This illustrates sequential causation. This requires causal undercutting for
causal implication.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired. But I also know that he will be resuscitated later, and then he will
be alive.  Should I conclude that Jones becomes dead? This version is solved incorrectly."
  :reasons
   neg-at-elimination
   *TEMPORAL-PROJECTION*
   *CAUSAL-UNDERCUTTER*
   *CAUSAL-IMPLICATION*
   neg-at-intro
   neg-at-intro2
   :inputs
   :premises
   ("(the_gun_is_loaded at 20)" 1.0)
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(Jones_is_resuscitated at 45)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   ("(Jones_is_resuscitated when ~(Jones is alive) is causally sufficient for
                           (Jones is alive) after an interval 5)" 1.0)
   :interests
    ("(? ((Jones is alive) at 60))" 0.75)
   )
;======================================================================
(make-simulation-problem
 :number  14
 :message
  "This illustrates sequential causation. This requires causal undercutting for
causal implication.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired. But I also know that he will be resuscitated later, and then he will
be alive.  Should I conclude that Jones becomes dead?"
  :reasons
   neg-at-elimination
   *TEMPORAL-PROJECTION*
   *CAUSAL-UNDERCUTTER*
   *CAUSAL-IMPLICATION*
   *CAUSAL-UNDERCUTTER-FOR-CAUSAL-IMPLICATION*
   neg-at-intro
   neg-at-intro2
   :inputs
   :premises
   ("(the_gun_is_loaded at 20)" 1.0)
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(Jones_is_resuscitated at 45)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   ("(Jones_is_resuscitated when ~(Jones is alive) is causally sufficient for
                           (Jones is alive) after an interval 5)" 1.0)
   :interests
    ("(? ((Jones is alive) at 60))" 0.75)
   )
;======================================================================
(make-simulation-problem
 :number  8
 :message
  "This is the indexical Yale Shooting Problem.  I know that the gun being fired while loaded
will cause Jones to become dead.  I know that the gun is initially loaded, and Jones is initially
alive.  Later, the gun is fired.  Should I conclude that Jones becomes dead?"
  :reasons
   *INDEXICAL-TEMPORAL-PROJECTION*
   *TEMPORAL-PROJECTION*
   *INDEXICAL-CAUSAL-UNDERCUTTER*
   *INDEXICAL-CAUSAL-IMPLICATION*
   :start-time 50
   :inputs
   :premises
   ("((Jones is alive) at 20)" 1.0)
   ("(the_gun_is_loaded at 20)" 1.0)
   ("(the_gun_is_fired at 30)" 1.0)
   ("(the_gun_is_fired when the_gun_is_loaded is causally sufficient for
                           ~(Jones is alive) after an interval 10)" 1.0)
   :interests
   ("(? (Jones is alive))" 0.75)
   )

;======================================================================

(make-simulation-problem
  :number  9
  :message
  "1.  An interest in whether b1 and b2 collide at 10 generates an interest in their positions at 10.
Because we know their positions at 0, we adopt interest in their velocities between 0 and 10.

2.  We know the velocities at 0, and temporal-projection leads to an inference that those velocities
remain unchanged between 0 and 10.  From that we can compute the positions at 10, and infer
that b1 and b2 collide at 10.

3.  However, temporal projection also leads to an inference that the positions at 10 are the
same as those at 0.  Because the velocities at 0 are nonzero, causal undercutting defeats this
inference, leaving us with a unique conclusion regarding the positions at 10 (they are at (5.0 3.0)).
"
  :reasons
  neg-at-elimination
  &-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER*
  *COLLISION*
  *NEW-POSITION*
  *POSITION-INCOMPATIBILITY-1*
  *POSITION-INCOMPATIBILITY-2*
  strict-arithmetical-inequality
  arithmetical-inequality
  is-past-or-present
  neg-at-intro
  arithmetical-nonequality
  inequality-transitivity
  pair-nonidentity
  pair-nonidentity-at-time
  &-at-intro
  arithmetical-equality
  :inputs
  :premises
  ("((the position of b1 is (0.0 3.0)) at 0)" 1.0)
  ("((the position of b2 is (1.0 0.0)) at 0)" 1.0)
  ("(all b)(all x)(all y)(all vx)(all vy)
  ((the velocity of b is (vx vy))
     when ((the position of b is (x y)) & ~((vx vy) = (0.0 0.0)))
  is causally sufficient for ~(the position of b is (x y)) after an interval 0)" 1.0)
  ("((the velocity of b1 is (.5 0.0)) at 0)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 0)" 1.0)
  ("(5.0 = (0.0 + (0.5 * (10 - 0))))" 1.0)
  ("(3.0 = (3.0 + (0.0 * (10 - 0))))" 1.0)
  ("(5.0 = (1.0 + (0.4 * (10 - 0))))" 1.0)
  ("(3.0 = (0.0 + (0.3 * (10 - 0))))" 1.0)

  :interests
;  ("(? ((b1 and b2 collide) at 10))" 0.75)
  ("(? x)(? y) ((the position of b1 is (x y)) at 10)" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  10
  :message
"
1.  An interest in whether b1 and b2 collide at 10 generates an interest in their positions at 10.
Because we know their positions at 0, we adopt interest in their velocities between 0 and 10.

2.  We know the velocities at 0, and temporal-projection leads to an inference that those velocities
remain unchanged between 0 and 10.  From that we can compute the positions at 10, and infer
that b1 and b2 collide at 10.

3.  However, temporal projection also leads to an inference that the positions at 10 are the
same as those at 0.  Because the velocities at 0 are nonzero, causal undercutting defeats this
inference, leaving us with a unique conclusion regarding the positions at 10 (they are at (5.0 3.0)).
"
  :reasons
  neg-at-elimination
  &-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER*
  *COLLISION*
  *NEW-POSITION*
  *POSITION-INCOMPATIBILITY-1*
  *POSITION-INCOMPATIBILITY-2*
  strict-arithmetical-inequality
  arithmetical-inequality
  is-past-or-present
  neg-at-intro
  arithmetical-nonequality
  inequality-transitivity
  pair-nonidentity
  pair-nonidentity-at-time
  &-at-intro
  arithmetical-equality
  ; *CAUSAL-IMPLICATION*
  ; COLLISION-SYMMETRY
  ; *CAUSAL-UNDERCUTTER+*
  :inputs
  :premises
  ("((the position of b1 is (0.0 3.0)) at 0)" 1.0)
  ("((the position of b2 is (1.0 0.0)) at 0)" 1.0)
  ("(all b)(all x)(all y)(all vx)(all vy)
  ((the velocity of b is (vx vy))
     when ((the position of b is (x y)) & ~((vx vy) = (0.0 0.0)))
  is causally sufficient for ~(the position of b is (x y)) after an interval 0)" 1.0)
  ("((the velocity of b1 is (.5 0.0)) at 0)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 0)" 1.0)
  ("(5.0 = (0.0 + (0.5 * (10 - 0))))" 1.0)
  ("(3.0 = (3.0 + (0.0 * (10 - 0))))" 1.0)
  ("(5.0 = (1.0 + (0.4 * (10 - 0))))" 1.0)
  ("(3.0 = (0.0 + (0.3 * (10 - 0))))" 1.0)
 ; ("((0 + 0) < 10)" 1.0)

  :interests
  ("(? ((b1 and b2 collide) at 10))" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  11
  :message
  "1.  We are given the velocities of b1 and b2 at 0, and are told they collide at (5 3) at 10.
We are interested in the velocity of b1 at 20.

2.  By causal-implication, we can infer that the velocity of b1 at 20 is (.4 .3).

3.  By temporal projection, we can also infer that the velocity of b1 at 20 is (.5 .0).  But this
is defeated by causal-undercutter+, because we also know that if the velocity is (.4 .3) then
it is not (.5 .0).
"
  :reasons
  neg-at-elimination
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER+*
  *CAUSAL-UNDERCUTTER*
  *CAUSAL-IMPLICATION*
  *COLLISION*
  *NEW-POSITION*
  strict-arithmetical-inequality
  arithmetical-inequality
  is-past-or-present
  neg-at-intro
  arithmetical-nonequality
  inequality-transitivity
  :inputs
  :premises
  ("((the velocity of b1 is (.5 0.0)) at 10)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 10)" 1.0)
  ("(b1 is a dimensionless billiard ball)" 1.0)
  ("(b2 is a dimensionless billiard ball)" 1.0)
  ("((b1 and b2 collide) at 10)" 1.0)
  ("(((.5 expt 2) + (0.0 expt 2)) = ((.4 expt 2) + (.3 expt 2)))" 1.0)
  ("(same-mass b1 b2)" 1.0)
  ("(all b)(all time) (((the velocity of b is (0.4 0.3)) at time)
                              -> ~((the velocity of b is (0.5 0.0)) at time))" 1.0)
  ("(all b)(all time) (((the velocity of b is (0.5 0.0)) at time)
                              -> ~((the velocity of b is (0.4 0.3)) at time))" 1.0)
  ("(all b1)(all b2)(all v1x)(all v1y)(all v2x)(all v2y)
    ((((b1 is a dimensionless billiard ball) & (b2 is a dimensionless billiard ball))
      & ((same-mass b1 b2) & (((v1x expt 2) + (v1y expt 2)) = ((v2x expt 2) + (v2y expt 2)))))
      ->
      ((b1 and b2 collide)
         when (the velocity of b2 is (v2x v2y))
        is causally sufficient for (the velocity of b1 is (v2x v2y))
        after an interval 0))" 1.0)
  ("(all b1)(all b2)(all v1x)(all v1y)(all v2x)(all v2y)
    ((((b1 is a dimensionless billiard ball) & (b2 is a dimensionless billiard ball))
      & ((same-mass b1 b2) & (((v1x expt 2) + (v1y expt 2)) = ((v2x expt 2) + (v2y expt 2)))))
      ->
      ((b1 and b2 collide)
         when (the velocity of b1 is (v2x v2y))
        is causally sufficient for (the velocity of b2 is (v2x v2y))
        after an interval 0))" 1.0)

  :interests
  ("(? x)(? y) ((the velocity of b1 is (x y)) at 20)" 0.75)
  )

;======================================================================

(make-simulation-problem
  :number  12
  :message
"  This is the Extended Prediction Problem.

1.  We are given the velocities of b1 and b2 at 0, and are told they collide at (5 3) at 10.
We are interested in the position of b1 at 20.  Given knowledge of the position of b1 at 10,
this generates an interest in the velocity of b1 between 10 and 20.

2.  By causal-implication, we can infer that the velocity of b1 between 10 and 20 is (.4 .3).
From this we can compute that the position of b1 at 20 is (9.0 6.0).

3.  By temporal projection, we can also infer that the velocity of b1 at 20 is (.5 .0).  But this
is defeated by causal-undercutter, because we also know that if the velocity is (.4 .3) then
it is not (.5 .0).

4.  By temporal projection, we can infer that the position of b1 at 20 is the same as at 0.
But this is defeated by causal-undercutter, because we know that the velocity of b1 at 0
is nonzero.

5.  By temporal projection, we can infer that the position of b1 at 20 is the same as at 10.
This is defeated in the same fashion as (4), because we know the velocity of
b1 between 0 and 10, and we are given that 10 is between 0 and 10.
"
  :reasons
  *CAUSAL-IMPLICATION*
  *TEMPORAL-PROJECTION*
  *CAUSAL-UNDERCUTTER*
  *COLLISION*
  *NEW-POSITION*
  *POSITION-INCOMPATIBILITY*
  pair-nonidentity
  pair-nonidentity-at-time
  &-at-intro
  :inputs
  :premises
  ("((the position of b1 is (0.0 3.0)) at 0)" 1.0)
  ("((the position of b2 is (1.0 0.0)) at 0)" 1.0)
  ("((the velocity of b1 is (.5 0.0)) at 0)" 1.0)
  ("((the velocity of b2 is (.4 .3)) at 0)" 1.0)
  ("(b1 is a dimensionless billiard ball)" 1.0)
  ("(b2 is a dimensionless billiard ball)" 1.0)
  ("(all b)(all x)(all y)(all vx)(all vy)
  ((the position of b is (x y))
     when ((the velocity of b is (vx vy)) & ~((vx vy) = (0.0 0.0)))
  is causally sufficient for ~(the position of b is (x y)) after an interval 0)" 1.0)
   ("(all b1)(all b2)(all v1x)(all v1y)(all v2x)(all v2y)
    ((((b1 is a dimensionless billiard ball) & (b2 is a dimensionless billiard ball))
      & ((same-mass b1 b2) & (((v1x expt 2) + (v1y expt 2)) = ((v2x expt 2) + (v2y expt 2)))))
      ->
      ((b1 and b2 collide)
         when (the velocity of b2 is (v2x v2y))
        is causally sufficient for (the velocity of b1 is (v2x v2y))
        after an interval 0))" 1.0)
  ("(same-mass b1 b2)" 1.0)
  ("(5.0 = (0.0 + (0.5 * (10 - 0))))" 1.0)
  ("(3.0 = (3.0 + (0.0 * (10 - 0))))" 1.0)
  ("(5.0 = (1.0 + (0.4 * (10 - 0))))" 1.0)
  ("(3.0 = (0.0 + (0.3 * (10 - 0))))" 1.0)
  ("(9.0 = (5.0 + (0.4 * (20 - 10))))" 1.0)
  ("(6.0 = (3.0 + (0.3 * (20 - 10))))" 1.0)
  ("(((.5 expt 2) + (0.0 expt 2)) = ((.4 expt 2) + (.3 expt 2)))" 1.0)

  :interests
  ("(? ((b1 and b2 collide) at 10))" 0.75)
 ; ("(? x)(? y) ((the velocity of b1 is (x y)) throughout (clopen 10 20))" 0.75)
  ("(? x)(? y) ((the position of b1 is (x y)) at 20)" 0.75)
  )
