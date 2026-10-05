import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_88 :
    (List.ofFn coreChunks509_88).flatten =
      (coreData509.take (coreResources509 88).q).drop 212 := by
  decide +kernel

theorem coreCheck509_88 :
    ∀ c : Fin 1, (coreChunks509_88 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 88)) = true := by
  decide +kernel
#print axioms coreFlatten509_88
#print axioms coreCheck509_88
end Erdos883Verified
