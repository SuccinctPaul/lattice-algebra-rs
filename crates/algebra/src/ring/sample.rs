use crate::ring::zq::Zq;
use rand::distr::uniform::{Error, SampleBorrow, SampleUniform, UniformInt, UniformSampler};
use rand::distr::Distribution;
use rand::Rng;

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

impl<const MODULUS: u64> Distribution<Zq<MODULUS>> for UniformZq<MODULUS> {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Zq<MODULUS> {
        self.0.sample(rng).into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Ring;
    use rand::distr::Distribution;
    use rand::rngs::ThreadRng;

    type Zq17 = Zq<17>;

    #[test]
    fn test_uniform_sampler_for_zq() {
        let mut rng = ThreadRng::default();
        let sampler = UniformZq::<17>::new(Zq17::ZERO, Zq17::new(16)).unwrap();
        for _ in 0..100 {
            let x = Distribution::sample(&sampler, &mut rng);
            assert!(x.value < 17);
        }
    }

    #[test]
    fn test_uniform_sampler_inclusive() {
        let mut rng = ThreadRng::default();
        let sampler = UniformZq::<17>::new_inclusive(Zq17::new(3), Zq17::new(10)).unwrap();
        for _ in 0..100 {
            let x = Distribution::sample(&sampler, &mut rng);
            assert!(x.value >= 3 && x.value <= 10);
        }
    }

    #[test]
    fn test_distribution_trait() {
        let mut rng = ThreadRng::default();
        let sampler = UniformZq::<17>::new(Zq17::ZERO, Zq17::new(16)).unwrap();
        for _ in 0..100 {
            let x = Distribution::sample(&sampler, &mut rng);
            assert!(x.value < 17);
        }
    }

    #[test]
    fn test_sampling_bounds() {
        let mut rng = ThreadRng::default();
        let sampler = UniformZq::<17>::new(Zq17::new(5), Zq17::new(15)).unwrap();
        for _ in 0..100 {
            let x = Distribution::sample(&sampler, &mut rng);
            assert!(x.value >= 5 && x.value < 15);
        }
    }
}
