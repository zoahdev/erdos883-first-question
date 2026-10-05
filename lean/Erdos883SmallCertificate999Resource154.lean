import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_154 :
    (List.ofFn coreChunks999_154).flatten =
      (coreData999.take (coreResources999 154).q).drop 281 := by
  decide +kernel

theorem coreCheck999_154 :
    ∀ c : Fin 1, (coreChunks999_154 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 154)) = true := by
  decide +kernel
#print axioms coreFlatten999_154
#print axioms coreCheck999_154
end Erdos883Verified
