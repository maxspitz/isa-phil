theory Philosophers imports Main begin

text \<open>Exercise 1 The Strict Positive Paradox\<close>

lemma strict_positive_paradox: "A \<longrightarrow> B \<longrightarrow> B"
proof (rule impI)
  show "B \<longrightarrow> B"
  proof (rule impI)
    assume "B"
    thus "B" .
  qed
qed

text \<open>Exercise 2\<close>

lemma prefixing: "(A \<longrightarrow> B) \<longrightarrow> (C \<longrightarrow> A) \<longrightarrow> (C \<longrightarrow> B)"
proof (rule impI)
  assume "A \<longrightarrow> B"
  show "(C \<longrightarrow> A) \<longrightarrow> (C \<longrightarrow> B)"
  proof (rule impI)
    assume "C \<longrightarrow> A"
    show "C \<longrightarrow> B"
    proof (rule impI)
      assume "C"
      with \<open>C \<longrightarrow> A\<close> have "A" by (rule mp)
      thus "B" using \<open>A \<longrightarrow> B\<close> by (rule rev_mp)
    qed
  qed
qed

lemma suffixing: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
proof (rule impI)
  assume "A \<longrightarrow> B"
  show "(B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  proof (rule impI)
    assume "B \<longrightarrow> C"
    show "A \<longrightarrow> C"
    proof (rule impI)
      assume "A"
      with \<open>A \<longrightarrow> B\<close> have "B" by (rule mp)
      thus "C" using \<open>B \<longrightarrow> C\<close> by (rule rev_mp)
    qed
  qed
qed

text \<open>Exercise 3\<close>

lemma "(A \<longleftrightarrow> B) \<longleftrightarrow> (B \<longleftrightarrow> A)"
proof (rule iffI)
  assume "A \<longleftrightarrow> B"
  show "B \<longleftrightarrow> A"
  proof (rule iffI)
    assume "B"
    with \<open>A \<longleftrightarrow> B\<close> show "A" by (rule iffD2)
  next
    assume "A"
    with \<open>A \<longleftrightarrow> B\<close> show "B" by (rule iffD1)
  qed
next
  assume "B \<longleftrightarrow> A"
  show "A \<longleftrightarrow> B"
  proof (rule iffI)
    assume "A"
    with \<open>B \<longleftrightarrow> A\<close> show "B" by (rule iffD2)
  next
    assume "B"
    with \<open>B \<longleftrightarrow> A\<close> show "A" by (rule iffD1)
  qed
qed

text \<open>Exercise 4 Strengthening the Antecedent\<close>

lemma strengthening_the_antecendent: "(A \<longrightarrow> C) \<longrightarrow>(A \<and> B \<longrightarrow> C)"
proof (rule impI)
  assume "A \<longrightarrow> C"
  show "A \<and> B \<longrightarrow> C"
  proof (rule impI)
    assume "A \<and> B"
    hence "A" by (rule conjE)
    with \<open>A \<longrightarrow> C\<close> show "C" by (rule mp)
  qed
qed

text \<open>Exercise 5\<close>

lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B \<and> C)"
proof (rule impI)
  assume "A \<longrightarrow> B"
  show "(A \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B \<and> C)"
  proof
    assume "A \<longrightarrow> C"
    show "A \<longrightarrow> B \<and> C"
    proof (rule impI)
      assume "A"
      then have "C" using \<open>A \<longrightarrow> C\<close> by (rule rev_mp)
      from \<open>A \<longrightarrow> B\<close> \<open>A\<close> have "B" by (rule mp)
      thus "B \<and> C" using \<open>C\<close> by (rule conjI)
    qed
  qed
qed

text \<open>Exercise 6\<close>

lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B \<or> C)"
proof
  assume "A \<longrightarrow> B"
  show "A \<longrightarrow> B \<or> C"
  proof
    assume "A"
    with \<open>A \<longrightarrow> B\<close> have "B" by (rule mp)
    thus "B \<or> C" by (rule disjI1)
  qed
qed

text \<open>Exercise 7\<close>

lemma "(A \<longrightarrow> C) \<and> (B \<longrightarrow> C) \<longrightarrow> (A \<or> B \<longrightarrow> C)"
proof
  assume antecedence: "(A \<longrightarrow> C) \<and> (B \<longrightarrow> C)"
  show "A \<or> B \<longrightarrow> C"
  proof
    assume "A \<or> B"
    show "C"
    proof (rule disjE)
      show "A \<or> B" using \<open>A \<or> B\<close> .
    next
      assume "A"
      from antecedence have "A \<longrightarrow> C" by (rule conjE)
      thus "C" using \<open>A\<close> by (rule mp)
    next
      assume "B"
      from antecedence have "B \<longrightarrow> C" by (rule conjE)
      with \<open>B\<close> show "C" by (rule rev_mp)
    qed
  qed
qed

text \<open>Exercise 8 The Associativity of Disjunction\<close>

lemma "A \<or> B \<or> C \<longleftrightarrow> (A \<or> B) \<or> C"
proof
  assume "A \<or> B \<or> C"
  show "(A \<or> B) \<or> C"
  proof (rule disjE)
    show "A \<or> B \<or> C" using \<open>A \<or> B \<or> C\<close> .
  next
    assume "A"
    hence "A \<or> B" by (rule disjI1)
    thus "(A \<or> B) \<or> C" ..
  next
    assume "B \<or> C"
    thus "(A \<or> B) \<or> C"
    proof (rule disjE)
      assume "B"
      hence "A \<or> B"  by (rule disjI2)
      thus "(A \<or> B) \<or> C" ..
    next
      assume "C"
      thus "(A \<or> B) \<or> C" ..
    qed
  qed
next
  assume "(A \<or> B) \<or> C"
  thus "A \<or> B \<or> C"
  proof
    assume "A \<or> B"
    thus "A \<or> B \<or> C"
    proof
      assume "A"
      thus "A \<or> B \<or> C" ..
    next
      assume "B"
      hence "B \<or> C" ..
      thus "A \<or> B \<or> C" ..
    qed
  next
    assume "C"
    hence "B \<or> C" ..
    thus "A \<or> B \<or> C" ..
  qed
qed

text \<open>Exercise 9\<close>

lemma "A \<or> B \<and> C \<longrightarrow> (A \<or> B) \<and> (A \<or> C)"
proof
  assume "A \<or> B \<and> C"
  thus "(A \<or> B) \<and> (A \<or> C)"
  proof
    assume "A"
    hence "A \<or> B" by (rule disjI1)
    from \<open>A\<close> have "A \<or> C" ..
    with \<open>A \<or> B\<close> show "(A \<or> B) \<and> (A \<or> C)" by (rule conjI)
  next
    assume "B \<and> C"
    hence "B" by (rule conjE)
    hence "A \<or> B" ..
    have "C" using \<open>B \<and> C\<close> ..
    hence "A \<or> C" ..
    with \<open>A \<or> B\<close> show "(A \<or> B) \<and> (A \<or> C)" ..
  qed
qed

text \<open>Exercise 10 Explosion\<close>

lemma explosion: "A \<and> \<not> A \<longrightarrow> B"
proof
  assume "A \<and> \<not> A"
  hence "A" by (rule conjE)
  have "\<not> A" using \<open>A \<and> \<not> A\<close> ..
  thus "B" using \<open>A\<close> by (rule notE)
qed

text \<open>Exercise 11\<close>

lemma "A \<or> B \<longrightarrow> \<not> A \<longrightarrow> B"
proof
  assume "A \<or> B"
  thus "\<not> A \<longrightarrow> B"
  proof
    assume "A"
    show "\<not> A \<longrightarrow> B"
    proof
      assume "\<not> A"
      thus "B" using \<open>A\<close> ..
    qed
  next
    assume "B"
    show "\<not> A \<longrightarrow> B"
    proof
      show "B" using \<open>B\<close> .
    qed
  qed
qed

text \<open>Exercise 12\<close>

lemma "A \<longrightarrow> \<not> \<not> A"
proof
  assume "A"
  show "\<not> \<not> A"
  proof (rule notI)
    assume "\<not> A"
    thus "False" using \<open>A\<close> by (rule notE)
  qed
qed

text \<open>Exercise 13\<close>

lemma "\<not> \<not> (A \<or> \<not> A)"
proof (rule notI)
  assume "\<not> (A \<or> \<not> A)"
  moreover have "A \<or> \<not> A"
  proof (rule disjI2)
    show "\<not> A "
    proof (rule notI)
      assume "A"
      hence "A \<or> \<not> A" by (rule disjI1)
      with \<open>\<not> (A \<or> \<not> A)\<close> show "False" by (rule notE)
    qed
  qed
  ultimately show "False" ..
qed

text \<open>Exercise 14 The Law of Excluded Middle\<close>

lemma excluded_middle: "A \<or> \<not> A"
proof (rule ccontr)
  assume "\<not> (A \<or> \<not> A)"
  moreover have "A \<or> \<not> A"
  proof (rule disjI2)
    show "\<not> A "
    proof (rule notI)
      assume "A"
      hence "A \<or> \<not> A" by (rule disjI1)
      with \<open>\<not> (A \<or> \<not> A)\<close> show "False" by (rule notE)
    qed
  qed
  ultimately show "False" ..
qed

text \<open>Exercise 15 Conditional Excluded Middle\<close>

lemma "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)"
proof cases
  assume "B"
  have "A \<longrightarrow> B"
  proof
    show "B" using \<open>B\<close> .
  qed
  thus "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)" ..
next
  assume "\<not> B"
  have "A \<longrightarrow> \<not> B"
  proof
    show "\<not> B" using \<open>\<not> B\<close> .
  qed
  thus "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)" ..
qed

text \<open>Exercise 16\<close>

lemma "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)"
proof cases
  assume "A \<longrightarrow> B"
  then show "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" ..
next
  assume "\<not> (A \<longrightarrow> B)"
  have "A"
  proof (rule ccontr)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof
      assume "A"
      show "B"
      proof (rule ccontr)
        from \<open>\<not> A\<close> \<open>A\<close> show "False" ..
      qed
    qed
    with \<open>\<not> (A \<longrightarrow> B)\<close> show "False" ..
  qed
  have "B \<longrightarrow> A"
  proof
    show "A" using \<open>A\<close> .
  qed
  thus "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" ..
qed

text \<open>Exercise 17\<close>

lemma "(A \<or> B) \<and> (A \<or> C) \<longrightarrow> A \<or> B \<and> C"
proof
  assume "(A \<or> B) \<and> (A \<or> C)"
  show "A \<or> B \<and> C"
  proof cases
    assume "A"
    thus "A \<or> B \<and> C" ..
  next
    assume "\<not> A"
    have "B \<and> C"
    proof
      show "B"
      proof (rule ccontr)
        assume "\<not> B"
        have "\<not> (A \<or> B)"
        proof
          assume "A \<or> B"
          thus "False"
          proof
            assume "A"
            with \<open>\<not> A\<close> show "False" ..
          next
            assume "B"
            with \<open>\<not> B\<close> show "False" ..
          qed
        qed
        have "A \<or> B" using \<open>(A \<or> B) \<and> (A \<or> C)\<close> ..
        with \<open>\<not> (A \<or> B)\<close> show "False" ..
      qed
    next
      show "C"
      proof (rule ccontr)
        assume "\<not> C"
        have "\<not> (A \<or> C)"
        proof
          assume "A \<or> C"
          thus "False"
          proof
            assume "A"
            with \<open>\<not> A\<close> show "False" ..
          next
            assume "C"
            with \<open>\<not> C\<close> show "False" ..
          qed
        qed
        have "A \<or> C" using \<open>(A \<or> B) \<and> (A \<or> C)\<close> ..
        with \<open>\<not> (A \<or> C)\<close> show "False" ..
      qed
    qed
    thus "A \<or> B \<and> C" ..
  qed
qed

text \<open>Exercise 18 The Equivalence Thesis\<close>

lemma "(A \<longrightarrow> B) \<longleftrightarrow> (\<not> A \<or> B)"
proof
  assume "A \<longrightarrow> B"
  show "\<not> A \<or> B"
  proof cases
    assume "B"
    thus "\<not> A \<or> B" ..
  next
    assume "\<not> B"
    have "\<not> A"
    proof
      assume "A"
      with \<open>A \<longrightarrow> B\<close> have "B" by (rule mp)
      with \<open>\<not> B\<close> show "False" ..
    qed
    thus "\<not> A \<or> B" ..
  qed
next
  assume "\<not> A \<or> B"
  show "A \<longrightarrow> B"
  proof cases
    assume "B"
    show "A \<longrightarrow> B"
    proof
      show "B" using \<open>B\<close> .
    qed
  next
    assume "\<not> B"
    have "\<not> A"
    proof
      assume "A"
      have "\<not> (\<not> A \<or> B)"
      proof
        assume "\<not> A \<or> B"
        thus "False"
        proof
          assume "\<not> A"
          thus "False" using \<open>A\<close> ..
        next
          assume "B"
          with \<open>\<not> B\<close> show "False" ..
        qed
      qed
      thus "False" using \<open>\<not> A \<or> B\<close> ..
    qed
    show "A \<longrightarrow> B"
    proof
      assume "A"
      show "B"
      proof (rule ccontr)
        assume "\<not> B"
        have "\<not> (\<not> A \<or> B)"
        proof
          assume "\<not> A \<or> B"
          thus "False"
          proof
            assume "\<not> A"
            thus "False" using \<open>A\<close> ..
          next
            assume "B"
            with \<open>\<not> B\<close> show "False" ..
          qed
        qed
        thus "False" using \<open>\<not> A \<or> B\<close> ..
      qed
    qed
  qed
qed

lemma "(A \<longrightarrow> B) \<longleftrightarrow> \<not> (A \<and> \<not> B)"
proof
  assume "A \<longrightarrow> B"
  show "\<not> (A \<and> \<not> B)"
  proof
    assume "A \<and> \<not> B"
    hence "A" ..
    have "\<not> B" using \<open>A \<and> \<not> B\<close> ..
    have "\<not> (A \<longrightarrow> B)"
    proof
      assume "A \<longrightarrow> B"
      hence "B" using \<open>A\<close> ..
      with \<open>\<not> B\<close> show "False" ..
    qed
    thus "False" using \<open>A \<longrightarrow> B\<close> ..
  qed
next
  assume "\<not> (A \<and> \<not> B)"
  show "A \<longrightarrow> B"
  proof
    assume "A"
    show "B"
    proof (rule ccontr)
      assume "\<not> B"
      with \<open>A\<close> have "A \<and> \<not> B" ..
      with \<open>\<not> (A \<and> \<not> B)\<close> show "False" ..
    qed
  qed
qed

text \<open>Exercise 19 The Air Raid\<close>

lemma
  assumes 1: "A \<or> \<not> A"
  assumes 2: "A \<longrightarrow> B \<longrightarrow> A"
  assumes 3: "(B \<longrightarrow> A) \<longrightarrow> D"
  assumes 4: "\<not> A \<longrightarrow> C \<longrightarrow> \<not> A"
  assumes 5: "(C \<longrightarrow> \<not> A) \<longrightarrow> D"
  shows "D"
proof (rule disjE)
  from 1 show "A \<or> \<not> A" .
next
  assume "A"
  with 2 have "B \<longrightarrow> A" ..
  with 3 show "D" ..
next
  assume "\<not> A"
  with 4 have "C \<longrightarrow> \<not> A" ..
  with 5 show "D" ..
qed

text \<open>Exercise 20\<close>

lemma "(\<forall> x. F x) \<longrightarrow> F a \<and> F b"
proof
  assume "\<forall> x. F x"
  hence "F b" by (rule allE)
  have "F a" using \<open>\<forall> x. F x\<close> ..
  thus "F a \<and> F b" using \<open>F b\<close> ..
qed

text \<open>Exercise 21 The Riddle of Dracula\<close>

lemma "(\<forall> x. R x d) \<longrightarrow> (\<forall> z. R d z \<longrightarrow> z = m) \<longrightarrow> d = m"
proof
  assume "\<forall> x. R x d"
  hence "R d d" by (rule allE)
  show "(\<forall> z. R d z \<longrightarrow> z = m) \<longrightarrow> d = m"
  proof
    assume "\<forall> z. R d z \<longrightarrow> z = m"
    hence "R d d \<longrightarrow> d = m" ..
    thus "d = m" using \<open>R d d\<close> by (rule mp)
  qed
qed

text \<open>Exercise 22\<close>

lemma "(\<forall> x. F x \<and> G x) \<longrightarrow> (\<forall> x. F x)"
proof
  assume "\<forall> x. F x \<and> G x"
  show "\<forall> x. F x"
  proof (rule allI)
    fix x
    have "F x \<and> G x" using \<open>\<forall> x. F x \<and> G x\<close> by (rule allE)
    thus "F x" ..
  qed
qed

text \<open>Exercise 23\<close>

lemma "(\<forall> x. F x) \<longrightarrow> (\<forall> x. G x \<longrightarrow> F x)"
proof
  assume "\<forall> x. F x"
  show "\<forall> x. G x \<longrightarrow> F x"
  proof (rule allI)
    fix x
    show "G x \<longrightarrow> F x"
    proof
      from \<open>\<forall> x. F x\<close> have "F x" by (rule allE)
      thus "F x" .
    qed
  qed
qed

text \<open>Exercise 24 The Converse Drinkers Principle\<close>

lemma "\<exists>x. (\<exists>y. F y) \<longrightarrow> F x"
proof cases
  assume "\<exists>y. F y"
  thus "\<exists>x. (\<exists>y. F y) \<longrightarrow> F x"
  proof (rule exE)
    fix y
    assume "F y"
    hence "(\<exists>y. F y) \<longrightarrow> F y" by (rule impI)
    thus "\<exists>x. (\<exists>y. F y) \<longrightarrow> F x" by (rule exI)
  qed
next
  fix y
  assume "\<nexists>y. F y"
  have "(\<exists>y. F y) \<longrightarrow> F y"
  proof
    assume "\<exists>y. F y"
    show "F y"
    proof (rule ccontr)
      from \<open>\<nexists>y. F y\<close> \<open>\<exists>y. F y\<close> show "False" ..
    qed
  qed
  thus "\<exists>x. (\<exists>y. F y) \<longrightarrow> F x" by (rule exI)
qed

text \<open>Exercise 25\<close>

lemma not_all_imp_some_not: "\<not> (\<forall>x. F x) \<longrightarrow> (\<exists>x. \<not> F x)"
proof
  assume "\<not> (\<forall>x. F x)"
  show "\<exists>x. \<not> F x"
  proof (rule ccontr)
    assume "\<nexists>x. \<not> F x"
    have "\<forall>x. F x"
    proof (rule allI)
      fix x
      show "F x"
      proof (rule ccontr)
        assume "\<not> F x"
        hence "\<exists>x. \<not> F x" by (rule exI)
        with \<open>\<nexists>x. \<not> F x\<close> show "False" by (rule notE)
      qed
    qed
    with \<open>\<not> (\<forall>x. F x)\<close> show "False" ..
  qed
qed

text \<open>Exercise 26\<close>

lemma "(\<forall>x. F x) \<longrightarrow> (\<exists>x. F x)"
proof
  fix x
  assume "\<forall>x. F x"
  hence "F x" by (rule allE)
  thus "\<exists>x. F x" by (rule exI)
qed

text \<open>Exercise 27\<close>

lemma "(\<exists>x. F x) \<longrightarrow> (\<exists>x. F x \<or> G x)"
proof
  assume "\<exists>x. F x"
  then obtain x where "F x" by (rule exE)
  hence "F x \<or> G x" ..
  thus "\<exists>x. F x \<or> G x" by (rule exI)
qed

text \<open>Exercise 28 The Drinker Principle\<close>

lemma "\<exists>x. F x \<longrightarrow> (\<forall>x. F x)"
proof cases
  fix x
  assume "\<forall>x. F x"
  hence "F x \<longrightarrow> (\<forall>x. F x)" by (rule impI)
  thus "\<exists>x. F x \<longrightarrow> (\<forall>x. F x)" by (rule exI)
next
  assume "\<not> (\<forall>x. F x)"
  with not_all_imp_some_not have "\<exists>x. \<not> F x" ..
  then obtain x where "\<not> F x" by (rule exE)
  have "F x \<longrightarrow> (\<forall>x. F x)"
  proof
    assume "F x"
    show "\<forall>x. F x"
    proof (rule ccontr)
      from \<open>\<not> F x\<close> \<open>F x\<close> show "False" ..
    qed
  qed
  thus "\<exists>x. F x \<longrightarrow> (\<forall>x. F x)" by (rule exI)
qed

text \<open>Exercise 29\<close>

lemma "F a \<longrightarrow> a = a"
proof
  show "a = a" by (rule refl)
qed

text \<open>Exercise 30\<close>

lemma "\<forall>x. \<exists>y. x = y"
proof (rule allI)
  fix x
  have "x = x" by (rule refl)
  thus "\<exists>y. x = y" by (rule exI)
qed

text \<open>Exercise 31\<close>

lemma "a = b \<longrightarrow> b = a"
proof
  assume "a = b"
  have "((=) b) b" ..
  with \<open>a = b\<close> show "((=) b) a" by (rule ssubst)
qed

text \<open>Exercise 32\<close>

lemma "a = b \<longrightarrow> b = c \<longrightarrow> a = c"
proof
  assume "a = b"
  show "b = c \<longrightarrow> a = c"
  proof
    assume "b = c"
    thus "a = c" using \<open>a = b\<close> by (rule subst)
  qed
qed

text \<open>Exercise 33 The Indiscernibility of Identity\<close>

lemma "x = y \<longrightarrow> (F x \<longleftrightarrow> F y)"
proof
  assume "x = y"
  show "F x \<longleftrightarrow> F y"
  proof
    assume "F x"
    with \<open>x = y\<close> show "F y" by (rule subst)
  next
    assume "F y"
    with \<open>x = y\<close> show "F x" by (rule ssubst)
  qed
qed

text \<open>Exercise 34\<close>

lemma "(\<forall>x. F x \<longleftrightarrow> x = a) \<longrightarrow> (THE x. F x) = a"
proof
  assume "\<forall>x. F x \<longleftrightarrow> x = a"
  then have "F a \<longleftrightarrow> a = a" ..
  moreover have "a = a" ..
  ultimately have "F a" by (rule iffD2)
  show "(THE x. F x) = a"
  proof (rule the_equality)
    show "F a" using \<open>F a\<close> .
  next
    fix x
    assume "F x"
    from \<open>\<forall>x. F x \<longleftrightarrow> x = a\<close> have "F x \<longleftrightarrow> x = a" ..
    thus "x = a" using \<open>F x\<close> ..
  qed
qed

end
