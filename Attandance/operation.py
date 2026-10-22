class operation:
    def addition(self, num):
        self.num = tuple(num)
        total = 0
        length = len(num)
        if length > 1 :
            for i in length:
                total += num[i]
        else:
            print("Required minimum 2 numbers to add")
        return total

if __name__ == "operation":
      operation()
             