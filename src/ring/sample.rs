use crate::ring::zq::Zq;
use rand::Rng;
use rand::distr::uniform::{Error, SampleBorrow, SampleUniform, UniformInt, UniformSampler};

// Make UniformZq generic over MODULUS
#[derive(Clone, Copy, Debug)]
pub struct UniformZq<const MODULUS: u64>(UniformInt<u64>);

impl<const MODULUS: u64> SampleUniform for Zq<MODULUS> {
    type Sampler = UniformZq<MODULUS>;
}

impl<const MODULUS: u64> UniformSampler for UniformZq<MODULUS> {
    type X = Zq<MODULUS>;

    fn new<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformInt::<u64>::new(low.borrow().value, high.borrow().value).map(UniformZq)
    }
    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformInt::<u64>::new_inclusive(low.borrow().value, high.borrow().value).map(UniformZq)
    }
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        self.0.sample(rng).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::ring::Ring;

    use super::*;
    use rand::thread_rng;

    type Zq17 = Zq<17>;

    // #[test]
    // fn test_sample_trait_for_zq() {
    //     let mut rng = thread_rng();
    //     for _ in 0..100 {
    //         let x: Zq17 = Sample::sample(&mut rng);
    //         assert!(x.abs() < 17);
    //     }
    // }

    #[test]
    #[ignore]
    fn test_uniform_sampler_for_zq() {
        let mut rng = thread_rng();
        let sampler = UniformZq::<17>::new(Zq17::ZERO, Zq17::new(222)).unwrap();
        for _ in 0..100 {
            let x = sampler.sample(&mut rng);
            assert!(x.abs() >= 3 && x.abs() < 10);
        }
        let sampler_inc = UniformZq::<17>::new_inclusive(Zq17::new(3), Zq17::new(10)).unwrap();
        for _ in 0..100 {
            let x = sampler_inc.sample(&mut rng);
            assert!(x.abs() >= 3 && x.abs() <= 10);
        }
    }
}
