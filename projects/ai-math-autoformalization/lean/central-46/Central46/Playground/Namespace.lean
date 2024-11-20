def a := 1

namespace A
def a := 2
namespace A
def a := 3
def _root := 3
#eval a
#eval A.a
end A
#eval _root_.a

namespace B
end B
end A
#eval a

namespace B
end B
