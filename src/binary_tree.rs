use core::ptr::NonNull;


pub struct BinaryTree {
    root: Option<NonNull<Node>>,
}

impl BinaryTree {
    pub fn inorder_tree_walk(&self) -> Option<Vec<i32>> {

        if self.root.is_some() {
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

    pub fn tree_successor(&mut self) -> Option<i32> {

        let node = self.successor();

        let result = self.process_result(node);

        result
        
    }

    pub fn tree_insert(&mut self, n: i32) {

        self.insert(Box::new(Node::new(n)));
    }

    pub fn tree_delete(&mut self, n: i32) {
        let node  = self.tree_search(self.root, n);

        if node.is_some() {
            self.delete(node)
        }
    }

    //private methods

    fn private_inorder_tree_walk(&self, x: Option<NonNull<Node>>, vec: &mut Vec<i32>) -> Vec<i32> {

        unsafe {

            let root = x.unwrap().as_ptr();
        
            if (*root).left.is_some() {
            
                self.private_inorder_tree_walk((*root).left, vec);
            }
            
            vec.push((*root).value);
        
            if (*root).right.is_some() {
                self.private_inorder_tree_walk((*root).right, vec);
            }
        }

        vec.to_vec()
    }
    
    fn process_result(&self, result: Option<NonNull<Node>>) -> Option<i32> {
        if result.is_some() {
            return unsafe { Some((*result.unwrap().as_ptr()).value)};
    
        } else {
            return None;
        }
    }

    fn tree_search(&self, x: Option<NonNull<Node>>, k: i32) -> Option<NonNull<Node>> {

        unsafe {

            if x.is_some() {

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

            while (*node).left.is_some() {
                node = (*node).left.unwrap().as_ptr()
            }

            NonNull::new(node)
        }
    }

    fn find_maximum(&self, x: Option<NonNull<Node>>) -> Option<NonNull<Node>> {

        unsafe {
            let mut node = x.unwrap().as_ptr();

            while (*node).right.is_some() {
                node = (*node).right.unwrap().as_ptr()
            }

            NonNull::new(node)
        }
    }

    fn successor(&mut self) -> Option<NonNull<Node>> {

        unsafe {
            if self.root.is_some() {
                let node = self.root.unwrap().as_ptr();
                return self.find_minimum((*node).right)

            } else {
                let node = self.root.unwrap().as_ptr();
                let mut y = (*node).parent;

                while y.is_some() && *node == (*(*(y.unwrap().as_ptr())).right.unwrap().as_ptr()) {
                    self.root = y;
                    y = (*y.unwrap().as_ptr()).parent;
                }
                y
            }
        }
    }

    fn insert(&mut self, node: Box<Node>) {

        unsafe {
            let mut x = self.root;
            let mut y = None;
    
            while x.is_some() {
                y = x;
                if node.value < (*(x.unwrap().as_ptr())).value {
                    x = (*(x.unwrap().as_ptr())).left;
                } else {
                    x = (*(x.unwrap().as_ptr())).right;
                }
            }

            let node_ptr = Box::into_raw(node);
            (*node_ptr).parent = y;
    
            if y.is_none() {
                self.root = NonNull::new(node_ptr);

            } else if (*node_ptr).value < (*(y.unwrap().as_ptr())).value {
                (*(y.unwrap().as_ptr())).left = NonNull::new(node_ptr);

            } else {
                (*(y.unwrap().as_ptr())).right = NonNull::new(node_ptr);
            }
        }
    }

    fn transplant(&mut self, u: Option<NonNull<Node>>, v: Option<NonNull<Node>>) {

        unsafe {
            let uu = u.unwrap().as_ptr();
            let u_parent = (*uu).parent;
            let u_left = (*(u_parent.unwrap()).as_ptr()).left;

            if u_parent.is_none() {
                self.root = v

            } else if u == u_left {
                (*(u_parent.unwrap()).as_ptr()).left = v

            } else {
                (*(u_parent.unwrap()).as_ptr()).right = v
            }

            if v.is_some() {
                (*(v.unwrap().as_ptr())).parent = u_parent
            }
        }
    }

    fn delete(&mut self, z: Option<NonNull<Node>>){
        unsafe {
            let zz = z.unwrap().as_ptr();
            let z_left = (*zz).left;
            let z_right = (*zz).right;

            if z_left.is_none() {
                self.transplant(z, z_right)

            } else if z_right.is_none() {
                self.transplant(z, z_left)

            } else {
                let y = self.find_minimum(z_right);
                let y_right = (*(y.unwrap().as_ptr())).right;
                let y_left = (*(y.unwrap().as_ptr())).left;

                if y != z_right {
                    self.transplant(y, y_right);
                    (*(y.unwrap().as_ptr())).right = (*zz).right;
                    (*(y_right.unwrap().as_ptr())).parent = y;
                }
                self.transplant(z, y);
                (*(y.unwrap().as_ptr())).left = z_left;
                (*(y_left.unwrap().as_ptr())).parent = y;
            }
        }
        
    }
        
}


#[derive(Debug, PartialEq)]
pub struct Node {
    value: i32,
    left: Option<NonNull<Node>>,
    right: Option<NonNull<Node>>,
    parent: Option<NonNull<Node>>,
}

impl Node {
    pub fn clone(&self) -> Self {

        let mut left = std::option::Option::None;
        let mut right = std::option::Option::None;
        let mut parent = std::option::Option::None;

        if self.left.is_some() {
            left = NonNull::new(self.left.unwrap().as_ptr());
        } else {
            left = None;
        }

        if self.right.is_some() {
            right = NonNull::new(self.right.unwrap().as_ptr());
        } else {
            right = None;
        }

        if self.parent.is_some() {
            parent = NonNull::new(self.parent.unwrap().as_ptr());
        } else {
            parent = None;
        }
    
        Node {
            value: self.value,
            left:  left,
            right: right,
            parent: parent,
        }
    }

    pub fn new(n: i32) -> Self {
        Node {
            value: n,
            left: None,
            right: None,
            parent: None,
        }
    }
}


#[cfg(test)]
mod tests {
    #[test]
    fn test_binary_tree() {
        use crate::binary_tree::BinaryTree;

        let mut tree = BinaryTree { root: None};
        
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
        assert_eq!(tree.tree_successor().unwrap(), 16);

        tree.tree_insert(30);

        assert!(tree.search(30).is_some());

        assert_eq!(tree.inorder_tree_walk().unwrap(), vec![1, 4, 5, 10, 16, 17, 21, 30]);

        tree.tree_delete(30);

        assert_eq!(tree.inorder_tree_walk().unwrap(), vec![1, 4, 5, 10, 16, 17, 21]);
    }
}
