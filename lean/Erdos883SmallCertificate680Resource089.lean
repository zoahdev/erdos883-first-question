import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_89 :
    (List.ofFn coreChunks680_89).flatten =
      (coreData680.take (coreResources680 89).q).drop 165 := by
  decide +kernel

theorem coreCheck680_89 :
    ∀ c : Fin 1, (coreChunks680_89 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 89)) = true := by
  decide +kernel
#print axioms coreFlatten680_89
#print axioms coreCheck680_89
end Erdos883Verified
