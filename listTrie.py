class TrieNode :
    def __init__(self, value) :
        self.value = value
        self.child = {}
        return

class listTrie :
    def __init__(self) :
        self.root = TrieNode('root')
        return

    def clear(self) :
        self.root = TrieNode('root')

    def insert(self, key, value) :
        temp = self.root
        for i in key :
            if i in temp.child :
                temp = temp.child[i]
            else :
                temp.child[i] = TrieNode(value)
                temp = temp.child[i]
        return
    
    def search(self, key) :
        # print(key)
        if len(key) == 0 :
            return None
        temp = self.root
        for i in key :
            if i in temp.child :
                temp = temp.child[i]
            else :
                return None
        return temp.value