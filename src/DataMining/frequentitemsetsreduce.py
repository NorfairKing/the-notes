# key: a hash of an itemset; value: a number of occurrences of that itemset
def reduce(key, values):
    total = 0
    for v in values:
        total += v
    if total > K:
        emit(key, total)
