import z3

letter_to_index_map = {letter: index for index, letter in enumerate("abcdefghijklmnopqrstuvwxyz")}
index_to_letter_map = {index: letter for letter, index in letter_to_index_map.items()}

word_length = 5

def define_letter_variables():
    return [z3.Int(f"letter_{index}") for index in range(word_length)]

def add_alphabet_modeling_constraints(solver, letter_vars):
    for letter_var in letter_vars:
        solver.add(letter_var >= 0, letter_var <= 25)

    return solver

def pretty_print_solution(model, letter_vars):
    word = []
    for index, letter_var in enumerate(letter_vars):
        word.append(index_to_letter_map[model[letter_var].as_long()])

    print(''.join(word))

def remove_plurals(words):
    five_letter_words = list(filter(lambda word: len(word) == 5, words))
    four_letter_words = set(filter(lambda word: len(word) == 4, words))
    all_five_letter_words_ending_in_s = set(filter(lambda word: word[4] == "s", five_letter_words))
    singular_five_letter_words = list(filter(lambda word: not (word in all_five_letter_words_ending_in_s and word[:4] in four_letter_words), five_letter_words))
    return singular_five_letter_words

def remove_words_with_invalid_chars(words):
    valid_chars_set = set(letter_to_index_map.keys())

    def contains_only_valid_chars(word):
        return set(word).issubset(valid_chars_set)

    return filter(contains_only_valid_chars, words)

def load_dictionary(dictionary_path=None):
    with open(dictionary_path, "r") as f:
        words_and_freq = {word_and_freq.split(' ')[0].strip(): int(word_and_freq.split(' ')[1]) for word_and_freq in f.readlines()}
        words_in_dict_set = set(words_and_freq.keys())

    words = remove_words_with_invalid_chars(words_in_dict_set)
    words = list(words)
    words = remove_plurals(words)

    all_legal_words_set = set(words)

    print(words)
    sum_frequencies = sum([freq for word, freq in words_and_freq.items() if word in all_legal_words_set])
    word_to_freq = {word: (freq / sum_frequencies) for word, freq in words_and_freq.items() if word in all_legal_words_set}
    print(word_to_freq)

    return words, word_to_freq

def add_legal_words_constraints(solver, words, letter_vars):
    all_words_disjunction = []

    for word in words:
        word_conjuction = z3.And([letter_vars[index] == letter_to_index_map[letter] for index, letter in enumerate(word)])
        all_words_disjunction.append(word_conjuction)

    solver.add(z3.Or(all_words_disjunction))

    return solver

def add_doesnt_contain_letter_constraint(solver, letter_vars, letter):
    for letter_var in letter_vars:
        solver.add(letter_var != letter_to_index_map[letter])

    return solver

def add_contains_letter_constraint(solver, letter_vars, letter):
    solver.add(z3.Or([letter_var == letter_to_index_map[letter] for letter_var in letter_vars]))

    return solver

def add_invalid_position_constraint(solver, letter_vars, letter, position):
    solver.add(letter_vars[position] != letter_to_index_map[letter])

    return solver

def add_exact_letter_position_constraint(solver, letter_vars, letter, position):
    solver.add(letter_vars[position] == letter_to_index_map[letter])

    return solver

def add_letter_appears_once_constraint(solver, letter_vars, letter):
    unique_letter_disjunction = []

    for letter_var in letter_vars:
        this_letter_conjunction = [letter_var == letter_to_index_map[letter]]
        for other_letter_var in letter_vars:
            if letter_var == other_letter_var:
                continue
            this_letter_conjunction.append(other_letter_var != letter_to_index_map[letter])
        unique_letter_disjunction.append(z3.And(this_letter_conjunction))

    solver.add(z3.Or(unique_letter_disjunction))

    return solver

def optimize_search(solver, word_to_freq, letter_to_freq, letter_vars):

    def maximize_letter_frequency():
        for freq_var, letter_var in zip(letter_frequency_vars, letter_vars):
            for letter_index, letter in index_to_letter_map.items():
                solver.add(z3.Implies(letter_var == letter_index, freq_var == letter_to_freq[letter]))

    def maximize_word_frequency():
        for word, freq in word_to_freq.items():
            word_conjuction = z3.And([letter_vars[index] == letter_to_index_map[letter] for index, letter in enumerate(word)])
            solver.add(z3.Implies(word_conjuction, word_frequency == freq))


    letter_frequency_vars = [z3.Real(f"letter_{index}_frequency") for index in range(len(letter_vars))]
    letter_frequency_sum = z3.Real(f"letter_frequency_sum")

    word_frequency = z3.Real(f"word_frequency")

    # Each letter frequency can be [0, 1.0], we divide the sum by num of letters to get a normalized sum
    solver.add(letter_frequency_sum == (z3.Sum(letter_frequency_vars) / len(letter_vars)))

    maximize_letter_frequency()
    maximize_word_frequency()

    # We weight common words a bit higher than common letters
    # otherwise the solver goes for words like "eerie" and similar weirdness
    solver.maximize((0.7*word_frequency) + (0.3*letter_frequency_sum))

    return solver

def make_normalized_word_frequency_map(words):
    letter_to_freq = [0] * len(letter_to_index_map)
    for word in words:
        for letter in word:
            letter_to_freq[letter_to_index_map[letter]] += 1
    sum_freq = sum(letter_to_freq)
    letter_to_freq_normalized = {index_to_letter_map[index]: (freq / sum_freq) for index, freq in enumerate(letter_to_freq)}
    return letter_to_freq_normalized

if __name__ == "__main__":
    words, word_to_freq = load_dictionary(dictionary_path="./en_50k.txt")
    letter_to_freq = make_normalized_word_frequency_map(words)

    solver = z3.Optimize()
    letter_vars = define_letter_variables()
    solver = add_alphabet_modeling_constraints(solver, letter_vars)
    solver = add_legal_words_constraints(solver, words, letter_vars)
    solver = optimize_search(solver, word_to_freq, letter_to_freq, letter_vars)

    # Dynamic part
    for banned_letter in "badgvfi":
        solver = add_doesnt_contain_letter_constraint(solver, letter_vars, banned_letter)

    solver = add_letter_appears_once_constraint(solver, letter_vars, "e")

    solver = add_exact_letter_position_constraint(solver, letter_vars, "e", 2)
    solver = add_exact_letter_position_constraint(solver, letter_vars, "r", 3)
    solver = add_exact_letter_position_constraint(solver, letter_vars, "y", 4)
    # End dynamic part

    print("Solving...")
    result = solver.check()
    print(result)
    assert result == z3.sat

    model = solver.model()
    pretty_print_solution(model, letter_vars)