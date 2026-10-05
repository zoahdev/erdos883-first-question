import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_105 :
    (List.ofFn coreChunks618_105).flatten =
      (coreData618.take (coreResources618 105).q).drop 280 := by
  decide +kernel

theorem coreCheck618_105 :
    ∀ c : Fin 2, (coreChunks618_105 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 105)) = true := by
  decide +kernel
#print axioms coreFlatten618_105
#print axioms coreCheck618_105
end Erdos883Verified
