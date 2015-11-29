# key: document name; value: text of document
map(key, value):
    for w in value:
        emit(w, 1)
