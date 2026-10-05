import Erdos883AdaptiveSpan44342Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_2 : adaptiveNumericSpans44342_2.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_2 : adaptiveSpanEven44342_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_2 : adaptiveSpanEven44342_2.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_2 : adaptiveSpanEven44342_2.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_2 : adaptiveSpanWhole44342_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_2 : adaptiveSpanWhole44342_2.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_2 : adaptiveSpanWhole44342_2.spans = coreWholeSpans 0 adaptiveNumericSpans44342_2 := by
  decide +kernel
end Erdos883Verified
