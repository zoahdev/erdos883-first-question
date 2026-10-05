import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_112 :
    (List.ofFn coreChunks680_112).flatten =
      (coreData680.take (coreResources680 112).q).drop 228 := by
  decide +kernel

theorem coreCheck680_112 :
    ∀ c : Fin 1, (coreChunks680_112 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 112)) = true := by
  decide +kernel
#print axioms coreFlatten680_112
#print axioms coreCheck680_112
end Erdos883Verified
