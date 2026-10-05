import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_111 :
    (List.ofFn coreChunks999_111).flatten =
      (coreData999.take (coreResources999 111).q).drop 191 := by
  decide +kernel

theorem coreCheck999_111 :
    ∀ c : Fin 1, (coreChunks999_111 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 111)) = true := by
  decide +kernel
#print axioms coreFlatten999_111
#print axioms coreCheck999_111
end Erdos883Verified
