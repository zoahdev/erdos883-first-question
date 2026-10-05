import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_94 :
    (List.ofFn coreChunks509_94).flatten =
      (coreData509.take (coreResources509 94).q).drop 163 := by
  decide +kernel

theorem coreCheck509_94 :
    ∀ c : Fin 1, (coreChunks509_94 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 94)) = true := by
  decide +kernel
#print axioms coreFlatten509_94
#print axioms coreCheck509_94
end Erdos883Verified
