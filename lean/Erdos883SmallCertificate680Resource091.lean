import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_91 :
    (List.ofFn coreChunks680_91).flatten =
      (coreData680.take (coreResources680 91).q).drop 169 := by
  decide +kernel

theorem coreCheck680_91 :
    ∀ c : Fin 1, (coreChunks680_91 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 91)) = true := by
  decide +kernel
#print axioms coreFlatten680_91
#print axioms coreCheck680_91
end Erdos883Verified
