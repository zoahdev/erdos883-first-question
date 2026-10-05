import Erdos883AdaptiveSpan44342Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_1 : adaptiveNumericSpans44342_1.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_1 : adaptiveSpanEven44342_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_1 : adaptiveSpanEven44342_1.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_1 : adaptiveSpanEven44342_1.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_1 : adaptiveSpanWhole44342_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_1 : adaptiveSpanWhole44342_1.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_1 : adaptiveSpanWhole44342_1.spans = coreWholeSpans 0 adaptiveNumericSpans44342_1 := by
  decide +kernel
end Erdos883Verified
