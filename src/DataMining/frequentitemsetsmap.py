# key: transaction number; value: list of items in the transaction
def map(key, value):
    for ss in subsets(value):
        if cost(ss) >= P:
            emit(hash(ss), 1)
