import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_89 :
    (List.ofFn coreChunks509_89).flatten =
      (coreData509.take (coreResources509 89).q).drop 213 := by
  decide +kernel

theorem coreCheck509_89 :
    ∀ c : Fin 1, (coreChunks509_89 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 89)) = true := by
  decide +kernel
#print axioms coreFlatten509_89
#print axioms coreCheck509_89
end Erdos883Verified
