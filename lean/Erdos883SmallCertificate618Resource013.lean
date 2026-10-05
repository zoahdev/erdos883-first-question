import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_13 :
    (List.ofFn coreChunks618_13).flatten =
      (coreData618.take (coreResources618 13).q).drop 120 := by
  decide +kernel

theorem coreCheck618_13 :
    ∀ c : Fin 1, (coreChunks618_13 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 13)) = true := by
  decide +kernel
#print axioms coreFlatten618_13
#print axioms coreCheck618_13
end Erdos883Verified
