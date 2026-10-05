import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_63 :
    (List.ofFn coreChunks999_63).flatten =
      (coreData999.take (coreResources999 63).q).drop 240 := by
  decide +kernel

theorem coreCheck999_63 :
    ∀ c : Fin 1, (coreChunks999_63 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 63)) = true := by
  decide +kernel
#print axioms coreFlatten999_63
#print axioms coreCheck999_63
end Erdos883Verified
