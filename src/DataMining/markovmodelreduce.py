# key: a word; value: a list of words that have followed it
def reduce(key, values):
    freqdict = dict()
    for v in values:
        if v in freqdict:
            freqdict[v] = freqdict[v] + 1
        else:
            freqdict[v] = 1
    result = []
    for k in freqdict:
        result.append((k, freqdict[k] / len(values)))
    emit(key, result)
