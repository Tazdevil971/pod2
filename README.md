# pod2
Pod2 is a library enabling the usage of [Pod](https://en.wikipedia.org/wiki/Passive_data_structure) data types in rust.
## Example
```rust
use pod2::{Pod, Be, Le, FromPod};

// This will automagically derive Pod safely.
#[derive(Pod, Debug, Clone, Copy, PartialEq, Eq)]
// This, although not necessary, removes any paddings.
#[repr(C, packed)]
struct MyPodType {
    // Be<T> will store any underlying integer
    // as big endian.
    a: Be<u16>,
    // Le<T> will store any underlying integer
    // as little endian.
    b: Le<u16>,
    // This will just store them using the native
    // endianess of the device.
    c: u32
}

fn main() {
    let my_buf: &[u8] = &[
        // a 
        0x00, 0xff,
        // b
        0xff, 0x00,
        // c
        0xaa, 0xbb, 0xbb, 0xaa
    ];

    // Look at the documentation for all
    // available conversion functions.
    let my_pod_type = MyPodType::from_slice(my_buf)
        .expect("Wrong size");

    assert_eq!(
        my_pod_type, 
        &MyPodType {
            a: Be::from(0xff),
            b: Le::from(0xff),
            c: 0xaabbbbaa
        }
    );
}
```