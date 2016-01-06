def group(lst):
    for i in range(0, len(lst)):
        val = lst[i:i+2]
        if len(val) == 2:
            yield tuple(val)

# key: document name; value: list of words
def map(key, value):
    emit("BEG", value[0])
    for (w1, w2) in group(value):
        emit(w1, w2)
