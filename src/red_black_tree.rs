use core::ptr::NonNull;

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Color {
    Red,
    Black,
}

pub struct RedBlackTree {
    root: Option<NonNull<Node>>,
    nil: NonNull<Node>,
}

impl RedBlackTree {
    pub fn new() -> Self {
        let nil = NonNull::new(&mut Node::create_nil() as *mut _);
        RedBlackTree {
            root: nil,
            nil: nil.unwrap(),
        }
    }
    pub fn inorder_tree_walk(&self) -> Option<Vec<i32>> {

        if self.root != Some(self.nil) {
            let mut result = vec![];
            self.private_inorder_tree_walk(self.root, &mut result);
            Some(result)

        } else {
            None
        }
    }

    pub fn search(&self, k: i32) -> Option<i32> {

        let node  = self.tree_search(self.root, k);
        
        let result = self.process_result(node);

        result
    }

    pub fn tree_minimum(&self) -> Option<i32> {
        let node = self.find_minimum(self.root);
        
        let result = self.process_result(node);

        result

    }

    pub fn tree_maximum(&self) -> Option<i32> {
        let node = self.find_maximum(self.root);

        let result = self.process_result(node);

        result
    }

    pub fn tree_insert(&mut self, n: i32) {

        self.insert(Box::new(Node::new(n, Color::Red, self.nil)));
    }

    pub fn tree_delete(&mut self, n: i32) {
        let node  = self.tree_search(self.root, n);

        if node != Some(self.nil) {
            self.delete(node)
        }
    }

    //private methods

    fn private_inorder_tree_walk(&self, x: Option<NonNull<Node>>, vec: &mut Vec<i32>) -> Vec<i32> {

        unsafe {

            let root = x.unwrap().as_ptr();
        
            if (*root).left != Some(self.nil) {
            
                self.private_inorder_tree_walk((*root).left, vec);
            }
            
            vec.push((*root).value);
        
            if (*root).right != Some(self.nil) {
                self.private_inorder_tree_walk((*root).right, vec);
            }
        }

        vec.to_vec()
    }
    
    fn process_result(&self, result: Option<NonNull<Node>>) -> Option<i32> {
        if result != Some(self.nil) && result.is_some() {
            return unsafe { Some((*result.unwrap().as_ptr()).value)};
    
        } else {
            return None;
        }
    }

    fn tree_search(&self, x: Option<NonNull<Node>>, k: i32) -> Option<NonNull<Node>> {

        unsafe {

            if x != Some(self.nil) {

                let node = x.unwrap().as_ptr();

                if k == (*node).value {
                    return NonNull::new(node);
                
                } else {
                    if k < (*node).value {
                        self.tree_search((*node).left, k)

                    } else {
                        self.tree_search((*node).right, k)
                    }
                }

            } else {
                return None;
            }
            
        }
    }

    fn find_minimum(&self, x: Option<NonNull<Node>>) -> Option<NonNull<Node>> {

        unsafe {
            let mut node = x.unwrap().as_ptr();

            while (*node).left != Some(self.nil) {
                node = (*node).left.unwrap().as_ptr()
            }

            NonNull::new(node)
        }
    }

    fn find_maximum(&self, x: Option<NonNull<Node>>) -> Option<NonNull<Node>> {

        unsafe {
            let mut node = x.unwrap().as_ptr();

            while (*node).right != Some(self.nil) {
                node = (*node).right.unwrap().as_ptr()
            }

            NonNull::new(node)
        }
    }

    fn left_rotate(&mut self, x: Option<NonNull<Node>>) {

        unsafe {
            let y = (*(x.unwrap()).as_ptr()).right;

            let y_left = (*(y.unwrap()).as_ptr()).left;
            let x_parent =  (*(x.unwrap()).as_ptr()).parent;

            (*(x.unwrap()).as_ptr()).right = y_left;

            if y_left != Some(self.nil) {
                (*(y_left.unwrap()).as_ptr()).parent = x;
            }

            (*(y.unwrap()).as_ptr()).parent = (*(x.unwrap()).as_ptr()).parent;

            if x_parent == Some(self.nil) {
                self.root = y

            } else if x == (*(x_parent.unwrap()).as_ptr()).left {
                (*(x_parent.unwrap()).as_ptr()).left = y

            } else {
                (*(x_parent.unwrap()).as_ptr()).right = y
            }

            (*(y.unwrap()).as_ptr()).left = x;
            (*(x.unwrap()).as_ptr()).parent = y;
        }
    }

    fn right_rotate(&mut self, y: Option<NonNull<Node>>) {

        unsafe {
            let x = (*(y.unwrap()).as_ptr()).left;

            let x_right = (*(x.unwrap()).as_ptr()).right;
            let y_parent =  (*(y.unwrap()).as_ptr()).parent;

            (*(y.unwrap()).as_ptr()).left = x_right;

            if x_right != Some(self.nil) {
                (*(x_right.unwrap()).as_ptr()).parent = y;
            }

            (*(x.unwrap()).as_ptr()).parent = (*(y.unwrap()).as_ptr()).parent;

            if y_parent == Some(self.nil) {
                self.root = x

            } else if y == (*(y_parent.unwrap()).as_ptr()).right {
                (*(y_parent.unwrap()).as_ptr()).right = x

            } else {
                (*(y_parent.unwrap()).as_ptr()).left = x
            }

            (*(x.unwrap()).as_ptr()).right = y;
            (*(y.unwrap()).as_ptr()).parent = x;
        }
    }

    fn insert(&mut self, node: Box<Node>) {

        unsafe {
            let mut x = self.root;
            let mut y: NonNull<Node> = self.nil;
    
            while x != Some(self.nil) {
                y = x.unwrap();
                if node.value < (*(x.unwrap().as_ptr())).value {
                    x = (*(x.unwrap().as_ptr())).left;
                } else {
                    x = (*(x.unwrap().as_ptr())).right;
                }
            }

            let mut node_ptr = Box::into_raw(node);
        
            if y == self.nil {
                self.root = NonNull::new(node_ptr);

            } else if (*node_ptr).value < (*y.as_ptr()).value {
                (*y.as_ptr()).left = NonNull::new(node_ptr);

            } else {
                (*y.as_ptr()).right = NonNull::new(node_ptr);
            }

            (*node_ptr).parent = Some(y);
            (*node_ptr).right = Some(self.nil);
            (*node_ptr).left = Some(self.nil);

            self.insert_fixup(&mut node_ptr);
        }
    }

    fn insert_fixup(&mut self, z: &mut *mut Node) {

        unsafe {
            let z_parent = (*(*z)).parent.unwrap().as_ptr();
            while (*z_parent).color == Color::Red {

                let z_p_p_pointer = (*(*(*z)).parent.unwrap().as_ptr()).parent.unwrap().as_ptr();

                if (*(*z)).parent == (*z_p_p_pointer).left {

                    let y = (*z_p_p_pointer).right.unwrap().as_ptr();

                    if (*y).color == Color::Red {
                        
                        (*z_parent).color = Color::Black;
                        (*y).color = Color::Black;
                        (*z_p_p_pointer).color = Color::Red;
                        *z = z_p_p_pointer
                        
                    } else {
                        let zz = NonNull::new(*z);

                        if zz == (*z_parent).right {
                            *z = z_parent;

                            self.left_rotate(zz)
                        }

                        (*z_parent).color = Color::Black;
                        (*z_p_p_pointer).color = Color::Red;
                        self.right_rotate(NonNull::new(z_p_p_pointer))
                    }

                } else {
                    let y = (*z_p_p_pointer).left.unwrap().as_ptr();

                    if (*y).color == Color::Red {

                        (*z_parent).color = Color::Black;
                        (*y).color = Color::Black;
                        (*z_p_p_pointer).color = Color::Red;
                        *z = z_p_p_pointer

                    } else {
                        let zz = NonNull::new(*z);
                        
                        if zz == (*z_parent).left {
                            *z = z_parent;

                            self.right_rotate(zz)
                        }

                        (*z_parent).color = Color::Black;
                        (*z_p_p_pointer).color = Color::Red;
                        self.left_rotate(NonNull::new(z_p_p_pointer))
                    }
                }
            }
            (*self.root.unwrap().as_ptr()).color = Color::Black;
        }
    }

    fn transplant(&mut self, u: Option<NonNull<Node>>, v: Option<NonNull<Node>>) {

        unsafe {
            let uu = u.unwrap().as_ptr();
            let u_parent = (*uu).parent;
            let u_left = (*(u_parent.unwrap()).as_ptr()).left;

            if u_parent == Some(self.nil) {
                self.root = v

            } else if u == u_left {
                (*(u_parent.unwrap()).as_ptr()).left = v

            } else {
                (*(u_parent.unwrap()).as_ptr()).right = v
            }

            if v != Some(self.nil) {
                (*(v.unwrap().as_ptr())).parent = u_parent
            }
        }
    }

    fn delete(&mut self, z: Option<NonNull<Node>>){

        let mut y = z;
        let mut x = None;

        unsafe {
            let zz = z.unwrap().as_ptr();
            let z_left = (*zz).left;
            let z_right = (*zz).right;

            let mut y_original_color = &(*y.unwrap().as_ptr()).color;

            if z_left == Some(self.nil) {

                x = z_right;
                self.transplant(z, z_right)

            } else if z_right == Some(self.nil) {

                x = z_left;
                self.transplant(z, z_left)

            } else {
                y = self.find_minimum(z_right);

                y_original_color = &(*y.unwrap().as_ptr()).color;

                let y_right = (*(y.unwrap().as_ptr())).right;
                let y_left = (*(y.unwrap().as_ptr())).left;

                x = y_right;

                if y != z_right {
                    self.transplant(y, y_right);
                    (*(y.unwrap().as_ptr())).right = (*zz).right;
                    (*(y_right.unwrap().as_ptr())).parent = y;

                } else {
                    (*x.unwrap().as_ptr()).parent = y
                }

                self.transplant(z, y);
                (*(y.unwrap().as_ptr())).left = z_left;
                (*(y_left.unwrap().as_ptr())).parent = y;
                (*y.unwrap().as_ptr()).color = (*z.unwrap().as_ptr()).color;
            }

            if *y_original_color == Color::Black {
                self.delete_fixup(&mut x)
            }
        }
        
    }

    fn delete_fixup(&mut self, x: &mut Option<NonNull<Node>>) {

        let mut x_ptr = x.unwrap().as_ptr();

        unsafe {
            while NonNull::new(x_ptr) != self.root && (*x.unwrap().as_ptr()).color == Color::Black {
                let x_p_left = (*(*x_ptr).parent.unwrap().as_ptr()).left;
                let x_p_right = (*(*x_ptr).parent.unwrap().as_ptr()).right;
                let mut w = x_p_right;

                if NonNull::new(x_ptr) == x_p_left {

                    if w.unwrap().as_mut().color == Color::Red {
                        w.unwrap().as_mut().color = Color::Black;
                        (*x_ptr).parent.unwrap().as_mut().color = Color::Red;

                        self.left_rotate((*x_ptr).parent);

                        w = (*x_ptr).parent.unwrap().as_mut().right;
                    }

                    if w.unwrap().as_mut().left.unwrap().as_mut().color == Color::Black && w.unwrap().as_mut().right.unwrap().as_mut().color == Color::Black {
                        w.unwrap().as_mut().color = Color::Black;
                        *x = (*x_ptr).parent;

                    } else {
                        if w.unwrap().as_mut().right.unwrap().as_mut().color == Color::Black {
                            w.unwrap().as_mut().left.unwrap().as_mut().color = Color::Black;
                            w.unwrap().as_mut().color = Color::Red;
                            self.right_rotate(w);
                            w = x_p_left;
                        }
                        w.unwrap().as_mut().color = (*x_ptr).parent.unwrap().as_mut().color;
                        (*x_ptr).parent.unwrap().as_mut().color = Color::Black;
                        w.unwrap().as_mut().right.unwrap().as_mut().color;

                        self.left_rotate((*x_ptr).parent);
                    }

                } else {
                    w = x_p_left;
                    if w.unwrap().as_mut().color == Color::Red {
                        w.unwrap().as_mut().color = Color::Black;

                        (*x_ptr).parent.unwrap().as_mut().color = Color::Red;
                        self.right_rotate((*x_ptr).parent);
                        w = x_p_left;
                    }

                    if w.unwrap().as_mut().right.unwrap().as_mut().color == Color::Black && w.unwrap().as_mut().left.unwrap().as_mut().color == Color::Black {
                        w.unwrap().as_mut().color = Color::Red;
                        *x = x_p_left;

                    } else {
                        if w.unwrap().as_mut().left.unwrap().as_mut().color == Color::Black {
                            w.unwrap().as_mut().right.unwrap().as_mut().color = Color::Black;
                            w.unwrap().as_mut().color = Color::Red;
                            self.left_rotate(w);
                            w = x_p_left;
                        }
                        w.unwrap().as_mut().color = (*x_ptr).parent.unwrap().as_mut().color;
                        (*x_ptr).parent.unwrap().as_mut().color = Color::Black;
                        w.unwrap().as_mut().left.unwrap().as_mut().color = Color::Black;
                        self.right_rotate((*x_ptr).parent);
                        *x = self.root;
                    }
                }
            }
            (*x_ptr).color = Color::Black;
        }
    }
        
}


#[derive(Debug, PartialEq)]
pub struct Node {
    value: i32,
    left: Option<NonNull<Node>>,
    right: Option<NonNull<Node>>,
    parent: Option<NonNull<Node>>,
    color: Color,
}

impl Node {
    pub fn new(n: i32, color: Color, nil: NonNull<Node>) -> Self {
        Node {
            value: n,
            left: Some(nil),
            right: Some(nil),
            parent: Some(nil),
            color: color,
        }
    }

    pub fn create_nil() -> Self {
        Node {
            value: 0,
            left: None,
            right: None,
            parent: None,
            color: Color::Black,
        }
    }
}


#[cfg(test)]
mod tests {
    #[test]
    fn test_red_black_tree() {
        use crate::red_black_tree::RedBlackTree;

        let mut tree = RedBlackTree::new();
        
        tree.tree_insert(10);
        tree.tree_insert(4);
        tree.tree_insert(1);
        tree.tree_insert(5);
        tree.tree_insert(17);
        tree.tree_insert(16);
        tree.tree_insert(21);

        assert_eq!(tree.inorder_tree_walk().unwrap(), vec![1, 4, 5, 10, 16, 17, 21]);

        assert_eq!(tree.search(40), None);

        assert_eq!(tree.tree_minimum().unwrap(), 1);
        assert_eq!(tree.tree_maximum().unwrap(), 21);

        tree.tree_insert(30);

        assert!(tree.search(30).is_some());

        assert_eq!(tree.inorder_tree_walk().unwrap(), vec![1, 4, 5, 10, 16, 17, 21, 30]);

        tree.tree_delete(30);

        assert_eq!(tree.inorder_tree_walk().unwrap(), vec![1, 4, 5, 10, 16, 17, 21]);
    }
}
