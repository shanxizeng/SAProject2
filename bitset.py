class BitSet:
    def __init__(self, size):
        self.size = size
        self.bs = 0
        
    def get(self, pos):
        return (self.bs >> pos) & 1
    
    def set(self, pos):
        self.bs |= (1 << pos)
        
    def clear(self):
        self.bs = 0
        
    def count(self):
        sum = 0
        tmp = self.bs
        while tmp > 0:
            if tmp & 1: sum += 1
            tmp = tmp >> 1
        return sum
    
    def none(self):
        return self.bs == 0
    
    def full(self):
        return self.bs == ((1 << self.size) - 1)    
    
    def union(self, Set):
        b = BitSet(self.size)
        b.bs = self.bs | Set.bs
        return b
    
    def intersect(self, Set):
        b = BitSet(self.size)
        b.bs = self.bs & Set.bs
        return b
        
    def complement(self):
        b = BitSet(self.size)
        b.bs = self.bs ^ ((1<<self.size) - 1)
        return b
        
    def toString(self):
        Str = str()
        for i in range(self.size):
            if(self.get(i)): Str = '1' + Str
            else: Str = '0' + Str
        return Str
    
if __name__ == "__main__":
    s = BitSet(200)
    print(s.count())
    s.set(8)
    s.set(1000)
    print(s.get(3))
    print(s.get(1000))
    print(s.count())