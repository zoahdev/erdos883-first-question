import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_151 :
    (List.ofFn coreChunks999_151).flatten =
      (coreData999.take (coreResources999 151).q).drop 261 := by
  decide +kernel

theorem coreCheck999_151 :
    ∀ c : Fin 1, (coreChunks999_151 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 151)) = true := by
  decide +kernel
#print axioms coreFlatten999_151
#print axioms coreCheck999_151
end Erdos883Verified
