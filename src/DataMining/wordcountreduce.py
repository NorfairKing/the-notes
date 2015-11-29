# key: a word; value: an iterator over counts
reduce(key, values):
    result = 0
    for v in values:
        result += v
    emit(key, result)
