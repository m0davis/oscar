
(make-planning-problem-list

 (make-planning-problem
  :number 1
  :message  "A simple non-linear planning problem"
  :goal  "(at-school son)"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  simplify-=>
  :premises
  ("(at-home son)" .99)
  ("(needs-battery car)" .99)
  ("(auto-repair-shop shop)" .99)
  ("have-money" .99)
  ("have-phone-book" .99)
  ("~have-telephone" .99)
  ("((& ~have-telephone ask-phone-company-for-telephone) => have-telephone)" 1.0)
  ("(all x)(all y)((& (& (at-home x) (works y)) (drive-to-school x y)) => (& (at-school x) ~(at-home x)))" 1.0)
  ("(all y)(all z)((& (& (auto-repair-shop z) (needs-battery y) (knows-problem z)) (installs-battery-in z y)) => (& (works y) ~(needs-battery y)))" 1.0)
  ("(all z)((& (in-communication-with z) (instruct z)) => (knows-problem z))" 1.0)
  ("(all z)((& (& (know-phone-number z) have-telephone) (telephone z)) => (in-communication-with z))" 1.0)
  ("(all z)((& have-phone-book (look-up-number z)) => (know-phone-number z))" 1.0)
  )

 (make-planning-problem
  :number 2
  :message  "Defeat by undermining subgoals"
  :goal  "(at-school son)"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan
  embellished-protoplan-for-goal
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  :premises
  ("(at-home son)" .99)
  ("(needs-battery car)" .99)
  ("(auto-repair-shop shop)" .99)
  ("have-money" .99)
					; ("(in-communication-with shop)" .99)
  ("have-phone-book" .99)
  ("(have-possession-of car)" .99)
  ("(all x)(all y)((& (& (at-home x) (works y) (have-possession-of y)) (drive-to-school x y)) => (& (at-school x) ~(at-home x)))" 1.0)
  ("(all y)(all z)((& (& ~(have-possession-of y) (works y) have-money (fixed z y)) (pay-for-repair-of y z)) => (have-possession-of y))" 1.0)
  ("(all y)(all z)((& (& (auto-repair-shop z) (needs-battery y) (knows-problem z y)) (installs-battery-in z y)) => (& (works y) ~(needs-battery y) (fixed z y)))" 1.0)
  ("(all z)(all y)((& (& (auto-repair-shop z) (in-communication-with z) ) (instruct-to-fix z y)) => (& (knows-problem z y) ~(have-possession-of y)))" 1.0)
  ("(all z)((& (know-phone-number z) (telephone z)) => (in-communication-with z))" 1.0)
  ("(all z)((& have-phone-book (look-up-number z)) => (know-phone-number z))" 1.0)
  )

 (make-planning-problem
  :number 3
  :message
  :goal  "(know-beethoven-birthday & know-time)"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  :premises
  ("at-library" .99 nil t)
  ("((& at-library ask-librarian) => know-beethoven-birthday)" .99 nil t)
  ("((& at-clock read-clock) => know-time)" .99 nil t)
  ("((& at-library go-to-clock) => (& at-clock ~at-library))" .99 nil t)
  )

 (make-planning-problem
  :number 4
  :message  "Quantified version of 3."
  :goal  "((know-beethoven-birthday Horatio) & (know-time Horatio))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  :premises
  ("(at-library Horatio)" .99)
  ("(all x)((& (at-library x) (ask-librarian x)) => (know-beethoven-birthday x))" .99)
  ("(all x)((& (at-clock x) (read-clock x)) => (know-time x))" .99)
  ("(all x)((& (at-library x) (go-to-clock x)) => (& (at-clock x) ~(at-library x)))" .99)
  )

 (make-planning-problem
  :number 5
  :message  "Adds ordering constraints."
  :goal  "~target-alive"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  :premises
  ("target-alive" .99)
  ("at-bar" .99)
  ("have-gun" .99)
  ("see-man" .99)
  ("((& (& see-target gun-is-loaded) aim-and-shoot) => ~target-alive)" .99)
  ("((& see-man get-directions) => know-location)" .99)
  ("((& (& at-alley know-location) go-to-target) => (& ~at-alley see-target))" .99)
  ("((& (& have-gun have-bullets) load-gun) => gun-is-loaded)" .99)
  ("((& at-alley get-bullets) => have-bullets)" .99)
  ("((& at-bar go-to-alley) => (& at-alley ~see-man ~at-bar))" .99)
  )

 (make-planning-problem
  :number 6
  :message  "The Sussman anomoly"
  :goal  "((on A B) & (on B C))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  :premises
  ("(on-table B)" .99)
  ("(on-table A)" .99)
  ("(on C A)" .99)
  ("(clear C)" .99)
  ("(clear B)" .99)
  ("~(clear A)" .99)
  ("(all x)(all y)((& (& (clear x) (clear y)) (move x y)) => (& ~(clear y) (on x y)))" .99)
  ("(all x)(all y)((& (& (on x y) (clear x)) (move-to-table x)) => (& (clear y) (on-table x)))" .99)
  ("(all x)(all y)(all z)((& (& (on x y) (clear x) (clear z)) (move x z)) => (clear y))" .99)
  )

 (make-planning-problem
  :number 8
  :message ""
  :goal  "have-food"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
					; =>-adjunction
					; =>-neg1
					; =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  :premises
  ("~have-money" .99)
  ("~have-food" .99)
  ("~at-store" .99)
  ("((& ~have-money beg) => have-money)" .99)
  ("((& (at-store & have-money) buy-food) => (& have-food ~have-money))" .99)
  ("((& (~at-store & have-money) take-bus) => (& at-store ~have-money))" .99)
  )

 (make-planning-problem
  :number 9
  :message ""
  :goal  "have-food"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  :premises
  ("~have-money" .99)
  ("~have-food" .99)
  ("~at-store" .99)
  ("possess-item1" .99)
  ("possess-item2" .99)
  ("((& (& ~have-money possess-item1) sell-item1) => (& have-money ~possess-item1))" .99)
  ("((& (& ~have-money possess-item2) sell-item2) => (& have-money ~possess-item2))" .99)
  ("((& (at-store & have-money) buy-food) => (& have-food ~have-money))" .99)
  ("((& (~at-store & have-money) take-bus) => (& at-store ~have-money))" .99)
  )

 (make-planning-problem
  :number 10
  :message ""
  :goal  "fired"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  :premises
  ("lever-left" .99)
  ("~cocked" .99)
  ("((& ~lever-left push-left) => lever-left)" .99)
  ("((& (~lever-left & cocked) push-left) => (fired & ~cocked))" .99)
  ("((& (~lever-left & ~cocked) push-left) => cocked)" .99)
  ("((& lever-left push-right) => ~lever-left)" .99)
  )

 (make-planning-problem
  :number 11
  :message ""
  :goal  "fired"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  :premises
  ("lever-left" .99)
  ("~cocked1" .99)
  ("~cocked2" .99)
					; ("((& (lever-right & ~cocked2) push-left) => (lever-left & ~lever-right))" .99)
  ("((& lever-right push-left) => (lever-left & ~lever-right))" .99)
  ("((& (~lever-left & cocked2) push-left) => (fired & ~cocked2))" .99)
  ("((& (lever-right & ~cocked1) push-left) => cocked1)" .99)
  ("((& (& lever-right cocked1 ~cocked2) push-left) => (cocked2 & ~cocked1))" .99)
  ("((& lever-left push-right) => (lever-right & ~lever-left))" .99)
  )

 (make-planning-problem
  :number 12
  :message "One of Scott's problems. "
  :goal  "know-your-birthdate"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  :premises
  ("in-garage" .99)
  ("see-box" .99)
  ("((& in-garage go-in-house) => (& see-key in-house ~in-garage ~outside ~see-box))" .99)
  ("((& in-garage go-outside) => (& outside ~in-house ~in-garage ~see-box ~see-key))" .99)
  ("((& see-key get-key) => have-key)" .99)
  ("((& in-house go-to-garage) => (& in-garage ~in-house ~outside see-box ~see-key))" .99)
  ("((& (& have-key see-box) open-box) => have-document)" .99)
  ("((& (& have-document outside) read-document) => know-your-birthdate)"
   .99)
  )

 (make-planning-problem
  :number 13
  :message "Flat tire problem for planner 44"
  :goal
  "(& ( on wheel2 hub)
    ~( is-open boot))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("( wheel wheel1)" .99)
  ("( wheel wheel2)" .99)
  ("( isa-hub hub)" .99)
  ("( are-nuts nuts)" .99)
  ("( container boot)" .99)
  ("( intact wheel2)" .99)
  ("( in jack boot)" .99)
  ("( in pump boot)" .99)
  ("( in wheel2 boot)" .99)
  ("( in wrench boot)" .99)
  ("( on wheel1 hub)" .99)
  ("( on-ground hub)" .99)
  ("( tight nuts hub)" .99)
  ("~( locked boot)" .99)
  ("~( is-open boot)" .99)
  ("~( inflated wheel2)" .99)
  ("~( unfastened hub)" .99)
  ("(all x)( ((( container x) & (~( locked x) & ~( is-open x))) & ( open-up x)) => ( is-open x))" .99)
  ("(all x)( ((( container x) & ( is-open x)) & ( close x)) => ~( is-open x))" .99)
  ("(all x)(all y)( ((( container y) & (( in x y) & ( is-open y))) & ( fetch x y)) => (( have x) & ~( in x y)))" .99)
  ("(all x)(all y)( ((( container y) & (( have x) & ( is-open y))) & ( put-away x y)) => (~( have x) & ( in x y)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( tight x y) & ( on-ground y))))) & ( loosen x y)) => (( loose x y) & ~( tight x y)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( loose x y) & ( on-ground y))))) & ( tighten x y)) => (( tight x y) & ~( loose x y)))" .99)
  ("(all x)( ((( isa-hub x) & (( on-ground x) & ( have jack))) & ( jack-up x)) => (~( on-ground x) & ~( have jack)))" .99)
  ("(all x)( ((( isa-hub x) & ~( on-ground x)) & ( jack-down x)) => (( on-ground x) & ( have jack)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (~( unfastened y) & (( have wrench) & ( loose x y)))))) & ( undo x y)) => (( have x) & (( unfastened y) & (~( on x y) & ~( loose x y)))))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (( unfastened y) & (( have wrench) & ( have x)))))) & ( do-up x y)) => (( loose x y) & (~( unfastened y) & ~( have x))))" .99)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (~( on-ground y) & (( on x y) & ( unfastened y))))) & ( remove-wheel x y)) => (( have x) & (( wheeless y) & ~( on x y))))" .99)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (( have x) & (( wheeless y) & (( unfastened y) & ~( on-ground y)))))) & ( put-on-wheel x y)) => (( on x y) & (~( have x) & ~( wheeless y))))" .99)
  ("(all x)( ((( wheel x) & (( have pump) & (~( inflated x) & ( intact x)))) & ( inflate x)) => ( inflated x))" .99)
  )

 (make-planning-problem
  :number 14
  :message  "Pednault's briefcase example."
  :goal  "((at-office briefcase) & (at-home paycheck))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("(at-home briefcase)" .99)
  ("(at-home paycheck)" .99)
  ("(in-briefcase paycheck)" .99)
  ("(all x)((& (in-briefcase x) (remove-from-briefcase x)) => ~(in-briefcase x))" .99)
  ("((& (at-home briefcase) take-briefcase-to-office) => (at-office briefcase))" .99)
  ("(all x)((& (& (at-home briefcase) (in-briefcase x)) take-briefcase-to-office) => ~(at-home x))" .99)
  )

 (make-planning-problem
  :number 15
  :message "Flat tire problem with types for planner 41 using relativized quantifiers"
  :goal
					;  "(& ( on wheel2 hub)
					;        ( tight nuts hub))"
  "(& ~( is-open boot)
               ( in jack boot)
               ( in pump boot)
               ( in wheel1 boot)
               ( in wrench boot)
               ( tight nuts hub)
               ( inflated wheel2)
               ( on wheel2 hub))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  relativized-UI
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("(:type wheel1 wheel)" .99 nil t)
  ("(:type wheel2 wheel)" .99 nil t)
  ("(:type hub isa-hub)" .99 nil t)
  ("(:type nuts are-nuts)" .99 nil t)
  ("(:type boot container)" .99 nil t)
  ("( intact wheel2)" .99 nil t)
  ("( in jack boot)" .99 nil t)
  ("( in pump boot)" .99 nil t)
  ("( in wheel2 boot)" .99 nil t)
  ("( in wrench boot)" .99 nil t)
  ("( on wheel1 hub)" .99 nil t)
  ("( on-ground hub)" .99 nil t)
  ("( tight nuts hub)" .99 nil t)
  ("~( locked boot)" .99 nil t)
  ("~( is-open boot)" .99 nil t)
  ("~( inflated wheel2)" .99 nil t)
  ("~( unfastened hub)" .99 nil t)
  ("(all x :type container)( ((~( locked x) & ~( is-open x)) & ( open-up x)) => ( is-open x))" .99 nil t)
  ("(all x :type container)( (( is-open x) & ( close x)) => ~( is-open x))" .99 nil t)
  ("(all x)(all y :type container)( ((( in x y) & ( is-open y)) & ( fetch x y)) => (( have x) & ~( in x y)))" .99 nil t)
  ("(all x)(all y :type container)( ((( have x) & ( is-open y)) & ( put-away x y)) => (~( have x) & ( in x y)))" .99 nil t)
  ("(all x :type are-nuts)(all y :type isa-hub)( ((( have wrench) & (( tight x y) & ( on-ground y))) & ( loosen x y)) => (( loose x y) & ~( tight x y)))" .99 nil t)
  ("(all x :type are-nuts)(all y :type isa-hub)( ((( have wrench) & (( loose x y) & ( on-ground y))) & ( tighten x y)) => (( tight x y) & ~( loose x y)))" .99 nil t)
  ("(all x :type isa-hub)( ((( on-ground x) & ( have jack)) & ( jack-up x)) => (~( on-ground x) & ~( have jack)))" .99 nil t)
  ("(all x :type isa-hub)( (~( on-ground x) & ( jack-down x)) => (( on-ground x) & ( have jack)))" .99 nil t)
  ("(all x :type are-nuts)(all y :type isa-hub)( ((~( on-ground y) & (~( unfastened y) & (( have wrench) & ( loose x y)))) & ( undo x y)) => (( have x) & (( unfastened y) & (~( on x y) & ~( loose x y)))))" .99 nil t)
  ("(all x :type are-nuts)(all y :type isa-hub)( ((~( on-ground y) & (( unfastened y) & (( have wrench) & ( have x)))) & ( do-up x y)) => (( loose x y) & (~( unfastened y) & ~( have x))))" .99 nil t)
  ("(all x :type wheel)(all y :type isa-hub)( ((~( on-ground y) & (( on x y) & ( unfastened y))) & ( remove-wheel x y)) => (( have x) & (( wheeless y) & ~( on x y))))" .99 nil t)
  ("(all x :type wheel)(all y :type isa-hub)( ((( have x) & (( wheeless y) & (( unfastened y) & ~( on-ground y)))) & ( put-on-wheel x y)) => (( on x y) & (~( have x) & ~( wheeless y))))" .99 nil t)
  ("(all x :type wheel)( ((( have pump) & (~( inflated x) & ( intact x))) & ( inflate x)) => ( inflated x))" .99 nil t)
  )

 (make-planning-problem
  :number 16
  :message "Flat tire problem with types for planner 41"
  :goal
					; "(& ( on wheel2 hub)
					;       ( tight nuts hub)
					;       ( in wrench boot))"
  "(& ( on wheel2 hub)
               ( tight nuts hub))"
					;  "(& ~( is-open boot)
					;        ( in jack boot)
					;        ( in pump boot)
					;        ( in wheel1 boot)
					;        ( in wrench boot)
					;        ( tight nuts hub)
					;        ( inflated wheel2)
					;        ( on wheel2 hub))"
					;  "(& ( on wheel2 hub)
					;        ( tight nuts hub)
					;         ~( is-open boot)
					;        ( in jack boot)
					;        ( in pump boot)
					;        ( in wheel1 boot)
					;        ( inflated wheel2)
					;       )"
					;      ;  ( in wrench boot)
					;     ;   ( inflated wheel2)
					;     ; )"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  ;TODO type-instantiation
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  ;TODO embedded-type-instantiation
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("(:type wheel1 wheel)" .99 nil t)
  ("(:type wheel2 wheel)" .99 nil t)
  ("(:type hub isa-hub)" .99 nil t)
  ("(:type nuts are-nuts)" .99 nil t)
  ("(:type boot container)" .99 nil t)
  ("( intact wheel2)" .99 nil t)
  ("( in jack boot)" .99 nil t)
  ("( in pump boot)" .99 nil t)
  ("( in wheel2 boot)" .99 nil t)
  ("( in wrench boot)" .99 nil t)
  ("( on wheel1 hub)" .99 nil t)
  ("( on-ground hub)" .99 nil t)
  ("( tight nuts hub)" .99 nil t)
  ("~( locked boot)" .99 nil t)
  ("~( is-open boot)" .99 nil t)
  ("~( inflated wheel2)" .99 nil t)
  ("~( unfastened hub)" .99 nil t)
  ("(all x)( (((:type x container) & (~( locked x) & ~( is-open x))) & ( open-up x)) => ( is-open x))" .99 nil t)
  ("(all x)( (((:type x container) & ( is-open x)) & ( close x)) => ~( is-open x))" .99 nil t)
  ("(all x)(all y)( (((:type y container) & (( in x y) & ( is-open y))) & ( fetch x y)) => (( have x) & ~( in x y)))" .99 nil t)
  ("(all x)(all y)( (((:type y container) & (( have x) & ( is-open y))) & ( put-away x y)) => (~( have x) & ( in x y)))" .99 nil t)
  ("(all x)(all y)( (((:type x are-nuts) & ((:type y isa-hub) & (( have wrench) & (( tight x y) & ( on-ground y))))) & ( loosen x y)) => (( loose x y) & ~( tight x y)))" .99 nil t)
  ("(all x)(all y)( (((:type x are-nuts) & ((:type y isa-hub) & (( have wrench) & (( loose x y) & ( on-ground y))))) & ( tighten x y)) => (( tight x y) & ~( loose x y)))" .99 nil t)
  ("(all x)( (((:type x isa-hub) & (( on-ground x) & ( have jack))) & ( jack-up x)) => (~( on-ground x) & ~( have jack)))" .99 nil t)
  ("(all x)( (((:type x isa-hub) & ~( on-ground x)) & ( jack-down x)) => (( on-ground x) & ( have jack)))" .99 nil t)
  ("(all x)(all y)( (((:type x are-nuts) & ((:type y isa-hub) & (~( on-ground y) & (~( unfastened y) & (( have wrench) & ( loose x y)))))) & ( undo x y)) => (( have x) & (( unfastened y) & (~( on x y) & ~( loose x y)))))" .99 nil t)
  ("(all x)(all y)( (((:type x are-nuts) & ((:type y isa-hub) & (~( on-ground y) & (( unfastened y) & (( have wrench) & ( have x)))))) & ( do-up x y)) => (( loose x y) & (~( unfastened y) & ~( have x))))" .99 nil t)
  ("(all x)(all y)( (((:type x wheel) & ((:type y isa-hub) & (~( on-ground y) & (( on x y) & ( unfastened y))))) & ( remove-wheel x y)) => (( have x) & (( wheeless y) & ~( on x y))))" .99 nil t)
  ("(all x)(all y)( (((:type x wheel) & ((:type y isa-hub) & (( have x) & (( wheeless y) & (( unfastened y) & ~( on-ground y)))))) & ( put-on-wheel x y)) => (( on x y) & (~( have x) & ~( wheeless y))))" .99 nil t)
  ("(all x)( (((:type x wheel) & (( have pump) & (~( inflated x) & ( intact x)))) & ( inflate x)) => ( inflated x))" .99 nil t)
  )

 (make-planning-problem
  :number 17
  :message "Flat tire problem for planner 41"
  :goal
					;  "(& ( on wheel2 hub)
					;        ( tight nuts hub))"
  "(& ~( is-open boot)
               ( in jack boot)
               ( in pump boot)
               ( in wheel1 boot)
               ( in wrench boot)
               ( tight nuts hub)
               ( inflated wheel2)
               ( on wheel2 hub))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
					; relativized-UI
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("( wheel wheel1)" .99 nil t)
  ("( wheel wheel2)" .99 nil t)
  ("( isa-hub hub)" .99 nil t)
  ("( are-nuts nuts)" .99 nil t)
  ("( container boot)" .99 nil t)
  ("( intact wheel2)" .99 nil t)
  ("( in jack boot)" .99 nil t)
  ("( in pump boot)" .99 nil t)
  ("( in wheel2 boot)" .99 nil t)
  ("( in wrench boot)" .99 nil t)
  ("( on wheel1 hub)" .99 nil t)
  ("( on-ground hub)" .99 nil t)
  ("( tight nuts hub)" .99 nil t)
  ("~( locked boot)" .99 nil t)
  ("~( is-open boot)" .99 nil t)
  ("~( inflated wheel2)" .99 nil t)
  ("~( unfastened hub)" .99 nil t)
  ("(all x)( ((( container x) & (~( locked x) & ~( is-open x))) & ( open-up x)) => ( is-open x))" .99 nil t)
  ("(all x)( ((( container x) & ( is-open x)) & ( close x)) => ~( is-open x))" .99 nil t)
  ("(all x)(all y)( ((( container y) & (( in x y) & ( is-open y))) & ( fetch x y)) => (( have x) & ~( in x y)))" .99 nil t)
  ("(all x)(all y)( ((( container y) & (( have x) & ( is-open y))) & ( put-away x y)) => (~( have x) & ( in x y)))" .99 nil t)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( tight x y) & ( on-ground y))))) & ( loosen x y)) => (( loose x y) & ~( tight x y)))" .99 nil t)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( loose x y) & ( on-ground y))))) & ( tighten x y)) => (( tight x y) & ~( loose x y)))" .99 nil t)
  ("(all x)( ((( isa-hub x) & (( on-ground x) & ( have jack))) & ( jack-up x)) => (~( on-ground x) & ~( have jack)))" .99 nil t)
  ("(all x)( ((( isa-hub x) & ~( on-ground x)) & ( jack-down x)) => (( on-ground x) & ( have jack)))" .99 nil t)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (~( unfastened y) & (( have wrench) & ( loose x y)))))) & ( undo x y)) => (( have x) & (( unfastened y) & (~( on x y) & ~( loose x y)))))" .99 nil t)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (( unfastened y) & (( have wrench) & ( have x)))))) & ( do-up x y)) => (( loose x y) & (~( unfastened y) & ~( have x))))" .99 nil t)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (~( on-ground y) & (( on x y) & ( unfastened y))))) & ( remove-wheel x y)) => (( have x) & (( wheeless y) & ~( on x y))))" .99 nil t)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (( have x) & (( wheeless y) & (( unfastened y) & ~( on-ground y)))))) & ( put-on-wheel x y)) => (( on x y) & (~( have x) & ~( wheeless y))))" .99 nil t)
  ("(all x)( ((( wheel x) & (( have pump) & (~( inflated x) & ( intact x)))) & ( inflate x)) => ( inflated x))" .99 nil t)
  )

 (make-planning-problem
  :number 18
  :message "Flat tire problem for planner 36"
  :goal
					; "(wheel wheel1)"
					; "(isa-hub hub)"
					;  "~(on-ground hub)"                  ;; gets this
					;  "(unfastened hub)"                     ;; gets this
					;  "(wheeless hub)"                       ;; gets this
					;  "( on wheel2 hub)"                   ;; gets this
					;  "(loose nuts hub)"
					;   "(& ~(on-ground hub) (loose nuts hub))"
					;  "(& ( on wheel2 hub)
					;        ( tight nuts hub))"
					;  "(& ( on wheel2 hub)
					;        ( loose nuts hub))"
  "(& ( on wheel2 hub)
               ~( is-open boot))"
					;   "(& ~( is-open boot)
					;         ( in jack boot)
					;         ( in pump boot)
					;         ( in wheel1 boot)
					;         ( in wrench boot)
					;         ( tight nuts hub)
					;         ( inflated wheel2)
					;         ( on wheel2 hub))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  ;plan-node-result TODO: try to get plan-node-result to work and add back in
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("( wheel wheel1)" .99)
  ("( wheel wheel2)" .99)
  ("( isa-hub hub)" .99)
  ("( are-nuts nuts)" .99)
  ("( container boot)" .99)
  ("( intact wheel2)" .99)
  ("( in jack boot)" .99)
  ("( in pump boot)" .99)
  ("( in wheel2 boot)" .99)
  ("( in wrench boot)" .99)
  ("( on wheel1 hub)" .99)
  ("( on-ground hub)" .99)
  ("( tight nuts hub)" .99)
  ("~( locked boot)" .99)
  ("~( is-open boot)" .99)
  ("~( inflated wheel2)" .99)
  ("~( unfastened hub)" .99)
  ("(all x)( ((( container x) & (~( locked x) & ~( is-open x))) & ( open-up x)) => ( is-open x))" .99)
  ("(all x)( ((( container x) & ( is-open x)) & ( close x)) => ~( is-open x))" .99)
  ("(all x)(all y)( ((( container y) & (( in x y) & ( is-open y))) & ( fetch x y)) => (( have x) & ~( in x y)))" .99)
  ("(all x)(all y)( ((( container y) & (( have x) & ( is-open y))) & ( put-away x y)) => (~( have x) & ( in x y)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( tight x y) & ( on-ground y))))) & ( loosen x y)) => (( loose x y) & ~( tight x y)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( loose x y) & ( on-ground y))))) & ( tighten x y)) => (( tight x y) & ~( loose x y)))" .99)
  ("(all x)( ((( isa-hub x) & (( on-ground x) & ( have jack))) & ( jack-up x)) => (~( on-ground x) & ~( have jack)))" .99)
  ("(all x)( ((( isa-hub x) & ~( on-ground x)) & ( jack-down x)) => (( on-ground x) & ( have jack)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (~( unfastened y) & (( have wrench) & ( loose x y)))))) & ( undo x y)) => (( have x) & (( unfastened y) & (~( on x y) & ~( loose x y)))))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (( unfastened y) & (( have wrench) & ( have x)))))) & ( do-up x y)) => (( loose x y) & (~( unfastened y) & ~( have x))))" .99)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (~( on-ground y) & (( on x y) & ( unfastened y))))) & ( remove-wheel x y)) => (( have x) & (( wheeless y) & ~( on x y))))" .99)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (( have x) & (( wheeless y) & (( unfastened y) & ~( on-ground y)))))) & ( put-on-wheel x y)) => (( on x y) & (~( have x) & ~( wheeless y))))" .99)
  ("(all x)( ((( wheel x) & (( have pump) & (~( inflated x) & ( intact x)))) & ( inflate x)) => ( inflated x))" .99)
  )

 (make-planning-problem
  :number 19
  :message "Flat tire problem for planner 34"
  :goal
  "(& ( on wheel2 hub)
               ~( is-open boot))"
  :reasons
  protoplan
  null-plan
  goal-regression
  split-conjunctive-goal
  REUSE-NODES
  REUSE-NODE
  protoplan-for-goal
  REUSE-PLANS
  simplify-=>
  =>-adjunction
  =>-neg1
  =>-neg2
  undermine-causal-links
  undermine-embedded-causal-links
  plan-undermines-first-causal-link
  plan-undermines-another-causal-link
  plan-undermines-causal-link
  embellished-protoplan-for-goal
  embellished-protoplan
  embedded-null-plan
  split-embedded-conjunctive-goal
  embedded-goal-regression
  add-ordering-constraints
  add-embedded-ordering-constraints
  confrontation
  embedded-confrontation
  :premises
  ("( wheel wheel1)" .99)
  ("( wheel wheel2)" .99)
  ("( isa-hub hub)" .99)
  ("( are-nuts nuts)" .99)
  ("( container boot)" .99)
  ("( intact wheel2)" .99)
  ("( in jack boot)" .99)
  ("( in pump boot)" .99)
  ("( in wheel2 boot)" .99)
  ("( in wrench boot)" .99)
  ("( on wheel1 hub)" .99)
  ("( on-ground hub)" .99)
  ("( tight nuts hub)" .99)
  ("~( locked boot)" .99)
  ("~( is-open boot)" .99)
  ("~( inflated wheel2)" .99)
  ("~( unfastened hub)" .99)
  ("(all x)( ((( container x) & (~( locked x) & ~( is-open x))) & ( open-up x)) => ( is-open x))" .99)
  ("(all x)( ((( container x) & ( is-open x)) & ( close x)) => ~( is-open x))" .99)
  ("(all x)(all y)( ((( container y) & (( in x y) & ( is-open y))) & ( fetch x y)) => (( have x) & ~( in x y)))" .99)
  ("(all x)(all y)( ((( container y) & (( have x) & ( is-open y))) & ( put-away x y)) => (~( have x) & ( in x y)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( tight x y) & ( on-ground y))))) & ( loosen x y)) => (( loose x y) & ~( tight x y)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (( have wrench) & (( loose x y) & ( on-ground y))))) & ( tighten x y)) => (( tight x y) & ~( loose x y)))" .99)
  ("(all x)( ((( isa-hub x) & (( on-ground x) & ( have jack))) & ( jack-up x)) => (~( on-ground x) & ~( have jack)))" .99)
  ("(all x)( ((( isa-hub x) & ~( on-ground x)) & ( jack-down x)) => (( on-ground x) & ( have jack)))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (~( unfastened y) & (( have wrench) & ( loose x y)))))) & ( undo x y)) => (( have x) & (( unfastened y) & (~( on x y) & ~( loose x y)))))" .99)
  ("(all x)(all y)( ((( are-nuts x) & (( isa-hub y) & (~( on-ground y) & (( unfastened y) & (( have wrench) & ( have x)))))) & ( do-up x y)) => (( loose x y) & (~( unfastened y) & ~( have x))))" .99)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (~( on-ground y) & (( on x y) & ( unfastened y))))) & ( remove-wheel x y)) => (( have x) & (( wheeless y) & ~( on x y))))" .99)
  ("(all x)(all y)( ((( wheel x) & (( isa-hub y) & (( have x) & (( wheeless y) & (( unfastened y) & ~( on-ground y)))))) & ( put-on-wheel x y)) => (( on x y) & (~( have x) & ~( wheeless y))))" .99)
  ("(all x)( ((( wheel x) & (( have pump) & (~( inflated x) & ( intact x)))) & ( inflate x)) => ( inflated x))" .99)
  ))
